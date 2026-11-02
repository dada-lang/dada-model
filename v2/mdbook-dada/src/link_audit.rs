//! Review obligations derived from authored links, without additional Markdown metadata.
//!
//! Extraction and ordering are deterministic. Coverage, clarity, and the reasons
//! for retaining a forward reference are judgments retained as review evidence.
use crate::{
    evidence::{Conclusion, ReviewBundle, ReviewRecord},
    inventory::{hash, input_path, Input, Inventory},
    links::{Direction, LinkInventory, LinkOccurrence, LinkTarget, Location, SourceLinks, Target},
};
use anyhow::{ensure, Context, Result};
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
};

pub fn is_subject(subject: &str) -> bool {
    subject.starts_with("links.") && subject.contains('/')
}

pub fn coverage_subject(unit: &str) -> String {
    format!("links.coverage/{unit}")
}
pub fn target_subject(key: &str) -> String {
    format!("links.target/{}", hash(key.as_bytes()))
}
pub fn forward_subject(occurrence: &str) -> String {
    format!("links.forward/{}", hash(occurrence.as_bytes()))
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Manifest {
    Coverage {
        source: SourceLinks,
    },
    Target {
        target: Target,
    },
    Forward {
        source_unit: String,
        source: Location,
        occurrence: LinkOccurrence,
    },
}

impl Manifest {
    fn subject(&self) -> String {
        match self {
            Self::Coverage { source } => coverage_subject(&source.unit_id),
            Self::Target { target } => target_subject(&target.key),
            Self::Forward { occurrence, .. } => forward_subject(&occurrence.id),
        }
    }

    pub fn location(&self) -> &Location {
        match self {
            Self::Coverage { source } => &source.location,
            Self::Target { target } => &target.location,
            Self::Forward { occurrence, .. } => &occurrence.source,
        }
    }
}

/// One generated inventory is reused across an entire evidence check.
pub struct AuditInventory {
    pub links: LinkInventory,
    pub manifests: BTreeMap<String, Manifest>,
}

impl AuditInventory {
    pub fn build(inventory: &Inventory) -> Result<Self> {
        let links = LinkInventory::build(inventory)?;
        let mut manifests = BTreeMap::new();
        for source in links
            .sources
            .values()
            .filter(|source| source.audit_required)
        {
            let coverage = Manifest::Coverage {
                source: source.clone(),
            };
            manifests.insert(coverage.subject(), coverage);
            for occurrence in &source.occurrences {
                if let LinkTarget::Internal { target } = &occurrence.target {
                    let target = Manifest::Target {
                        target: target.clone(),
                    };
                    manifests.insert(target.subject(), target);
                    if matches!(
                        occurrence.direction,
                        Direction::Forward | Direction::Local | Direction::Unordered
                    ) {
                        let forward = Manifest::Forward {
                            source_unit: source.unit_id.clone(),
                            source: source.location.clone(),
                            occurrence: occurrence.clone(),
                        };
                        manifests.insert(forward.subject(), forward);
                    }
                }
            }
        }
        Ok(Self { links, manifests })
    }

    pub fn inputs(&self, inventory: &Inventory, subject: &str) -> Result<Vec<Input>> {
        let manifest = self
            .manifests
            .get(subject)
            .with_context(|| format!("unknown link audit subject {subject}"))?;
        let mut inputs = inventory.common_inputs()?;
        let location = manifest.location();
        inputs.push(Input::new(
            "audit:subject".into(),
            location.path.clone(),
            location.line,
            serde_json::to_string_pretty(manifest)?,
        ));
        // Source positions participate as content. Ordinary correspondence inputs
        // deliberately ignore line numbers, but moving a link changes its order.
        inputs.push(Input::new(
            "audit:reading-order".into(),
            self.links.summary_path.clone(),
            1,
            serde_json::to_string_pretty(&(&self.links.chapters, &self.links.cycles))?,
        ));
        let summary = fs::read_to_string(input_path(&inventory.root, &self.links.summary_path)?)?;
        inputs.push(Input::new(
            "context:link-summary".into(),
            self.links.summary_path.clone(),
            1,
            summary,
        ));
        let mut paths = BTreeSet::new();
        let mut selections = BTreeMap::new();
        let mut add_source = |unit: &str| -> Result<()> {
            let unit = inventory.unit(unit)?;
            paths.insert(unit.source_path.clone());
            let line = inventory.sources[&unit.source_path][..unit.range.start]
                .bytes()
                .filter(|b| *b == b'\n')
                .count()
                + 1;
            selections.insert(
                format!("audit:unit:{}", unit.id),
                Input::new(
                    format!("audit:unit:{}", unit.id),
                    unit.source_path.clone(),
                    line,
                    unit.raw.clone(),
                ),
            );
            Ok(())
        };
        let mut targets = Vec::new();
        match manifest {
            Manifest::Coverage { source } => {
                add_source(&source.unit_id)?;
                // These are author-declared conceptual context, including concepts
                // that a coverage review may find were not linked in the prose.
                for dependency in &inventory.unit(&source.unit_id)?.uses {
                    add_source(dependency)?;
                }
                for occurrence in &source.occurrences {
                    if let LinkTarget::Internal { target } = &occurrence.target {
                        targets.push(target);
                    }
                }
            }
            Manifest::Target { target } => targets.push(target),
            Manifest::Forward {
                source_unit,
                occurrence,
                ..
            } => {
                add_source(source_unit)?;
                if let LinkTarget::Internal { target } = &occurrence.target {
                    targets.push(target);
                }
            }
        }
        for target in targets {
            paths.insert(target.location.path.clone());
            let source = inventory
                .sources
                .get(&target.location.path)
                .context("link target chapter is absent")?;
            let content = source
                .get(target.location.range.clone())
                .context("invalid target range")?
                .to_owned();
            let key = format!("audit:target:{}", hash(target.key.as_bytes()));
            selections.insert(
                key.clone(),
                Input::new(
                    key,
                    target.location.path.clone(),
                    target.location.line,
                    content,
                ),
            );
        }
        inputs.extend(selections.into_values());
        for path in paths {
            inputs.push(Input::new(
                format!("context:link-chapter:{path}"),
                path.clone(),
                1,
                inventory.sources[&path].clone(),
            ));
        }
        inputs.sort_by(|a, b| a.key.cmp(&b.key));
        Ok(inputs)
    }
}

pub fn subjects(inventory: &Inventory) -> Result<BTreeSet<String>> {
    Ok(AuditInventory::build(inventory)?
        .manifests
        .into_keys()
        .collect())
}

pub fn inputs(inventory: &Inventory, subject: &str) -> Result<Vec<Input>> {
    AuditInventory::build(inventory)?.inputs(inventory, subject)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LinkRole {
    Conceptual,
    Navigation,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LinkAssessment {
    pub occurrence: String,
    pub role: LinkRole,
    pub rationale: String,
}

/// Absolute byte offsets in the snapshotted chapter, not a reviewer-supplied quote.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DefinitionSpan {
    pub path: String,
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum OrderAssessment {
    Forward {
        necessity: String,
        signposting: String,
        signpost: DefinitionSpan,
        minimal_use: String,
    },
    Backward {
        rationale: String,
    },
    Navigation {
        rationale: String,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Assessment {
    Coverage {
        prose: String,
        mathematics: String,
        links: Vec<LinkAssessment>,
    },
    Target {
        subject: String,
        definition: DefinitionSpan,
        clarity: String,
        independence: String,
    },
    Forward {
        assessment: OrderAssessment,
    },
}

pub fn manifest(bundle: &ReviewBundle) -> Result<Manifest> {
    let input = bundle
        .inputs
        .iter()
        .find(|input| input.key == "audit:subject")
        .context("link audit bundle lacks its generated subject manifest")?;
    let manifest: Manifest =
        serde_json::from_str(&input.content).context("invalid link audit manifest")?;
    ensure!(
        manifest.subject() == bundle.unit,
        "audit manifest names another subject"
    );
    Ok(manifest)
}

fn nonempty(errors: &mut Vec<String>, name: &str, text: &str) {
    if text.trim().is_empty() {
        errors.push(format!("link audit requires nonempty {name}"));
    }
}

fn span_errors(bundle: &ReviewBundle, span: &DefinitionSpan, enclosing: &Location) -> Vec<String> {
    let mut errors = Vec::new();
    let source = bundle
        .inputs
        .iter()
        .find(|input| input.key == format!("context:link-chapter:{}", enclosing.path));
    if span.path != enclosing.path
        || span.start < enclosing.range.start
        || span.end > enclosing.range.end
        || span.start >= span.end
    {
        errors.push(
            "reviewed span must be nonempty and inside the exact resolved source/target".into(),
        );
    }
    match source.and_then(|source| source.content.get(span.start..span.end)) {
        Some(text) if !text.trim().is_empty() => {}
        _ => errors
            .push("reviewed span must select nonempty UTF-8 text in the chapter snapshot".into()),
    }
    errors
}

/// Validate against the bundle's immutable manifest as well as the general
/// review schema. Current-source comparison remains the evidence engine's job.
pub fn validate_review(bundle: &ReviewBundle, review: &ReviewRecord) -> Vec<String> {
    if !is_subject(&bundle.unit) {
        return if review.audit.is_some() {
            vec!["correspondence review cannot carry a link audit assessment".into()]
        } else {
            Vec::new()
        };
    }
    let manifest = match manifest(bundle) {
        Ok(manifest) => manifest,
        Err(error) => return vec![format!("{error:#}")],
    };
    let Some(assessment) = &review.audit else {
        return vec!["link audit review requires a purpose-specific audit assessment".into()];
    };
    let mut errors = Vec::new();
    match (&manifest, assessment) {
        (
            Manifest::Coverage { source },
            Assessment::Coverage {
                prose,
                mathematics,
                links,
            },
        ) => {
            nonempty(&mut errors, "prose coverage rationale", prose);
            nonempty(&mut errors, "mathematics coverage rationale", mathematics);
            let expected: BTreeSet<_> = source
                .occurrences
                .iter()
                .map(|link| link.id.as_str())
                .collect();
            let actual: BTreeSet<_> = links.iter().map(|link| link.occurrence.as_str()).collect();
            if actual.len() != links.len() {
                errors.push("duplicate link occurrence assessment".into());
            }
            if actual != expected {
                errors
                    .push("coverage must classify exactly every generated link occurrence".into());
            }
            for link in links {
                nonempty(
                    &mut errors,
                    "link classification rationale",
                    &link.rationale,
                );
                if review.conclusion == Conclusion::Corresponds
                    && link.role == LinkRole::Conceptual
                    && source.occurrences.iter().any(|occurrence| {
                        occurrence.id == link.occurrence
                            && !matches!(occurrence.target, LinkTarget::Internal { .. })
                    })
                {
                    errors.push("conceptual links need a local, snapshotted defining target; external and asset links may only be navigation/source citations".into());
                }
            }
        }
        (
            Manifest::Target { target },
            Assessment::Target {
                subject,
                definition,
                clarity,
                independence,
            },
        ) => {
            nonempty(&mut errors, "target subject", subject);
            nonempty(&mut errors, "target clarity rationale", clarity);
            nonempty(&mut errors, "target independence rationale", independence);
            errors.extend(span_errors(bundle, definition, &target.location));
        }
        (Manifest::Forward { .. }, Assessment::Forward { assessment }) => match assessment {
            OrderAssessment::Forward {
                necessity,
                signposting,
                signpost,
                minimal_use,
            } => {
                for (name, value) in [
                    (
                        "necessity (including rearrangement alternatives)",
                        necessity,
                    ),
                    ("explicit forward signposting", signposting),
                    ("minimal reliance", minimal_use),
                ] {
                    nonempty(&mut errors, name, value);
                }
                // The source-unit range is independently derived and hashed in
                // the manifest, rather than trusting mutable retrieval line numbers.
                if let Manifest::Forward { source, .. } = &manifest {
                    errors.extend(span_errors(bundle, signpost, source));
                }
            }
            OrderAssessment::Backward { rationale } | OrderAssessment::Navigation { rationale } => {
                nonempty(&mut errors, "order disposition rationale", rationale)
            }
        },
        _ => {
            errors.push("audit assessment has the wrong purpose for this generated subject".into())
        }
    }
    errors
}

/// Cross-review consistency is checked from current, active positive records.
/// No review output is smuggled into another review's source hash. A later
/// classification or defining-span change therefore causes a new check.
pub fn cross_validate(
    audits: &AuditInventory,
    active: &BTreeMap<String, Vec<ReviewRecord>>,
) -> Vec<(String, String)> {
    let mut errors = Vec::new();
    let positives = |id: &str| -> Vec<&ReviewRecord> {
        active
            .get(id)
            .into_iter()
            .flatten()
            .filter(|review| review.conclusion == Conclusion::Corresponds)
            .collect()
    };
    // Independent positive reviews cannot disagree silently, even when the
    // link is unambiguously backward and needs no forward-reference subject.
    for (id, records) in active {
        match audits.manifests.get(id) {
            Some(Manifest::Coverage { source }) => {
                for occurrence in &source.occurrences {
                    let roles: BTreeSet<_> = records
                        .iter()
                        .filter_map(|review| match &review.audit {
                            Some(Assessment::Coverage { links, .. }) => links
                                .iter()
                                .find(|link| link.occurrence == occurrence.id)
                                .map(|link| match link.role {
                                    LinkRole::Conceptual => 0,
                                    LinkRole::Navigation => 1,
                                }),
                            _ => None,
                        })
                        .collect();
                    if roles.len() > 1 {
                        errors.push((
                            id.clone(),
                            format!("active coverage reviews disagree about {}", occurrence.id),
                        ));
                    }
                }
            }
            Some(Manifest::Target { .. }) => {
                let definitions: Vec<_> = records
                    .iter()
                    .filter_map(|review| match &review.audit {
                        Some(Assessment::Target { definition, .. }) => Some(definition),
                        _ => None,
                    })
                    .collect();
                if definitions.windows(2).any(|pair| pair[0] != pair[1]) {
                    errors.push((
                        id.clone(),
                        "active target reviews disagree about the defining occurrence".into(),
                    ));
                }
            }
            _ => {}
        }
    }
    for (id, records) in active {
        let Some(Manifest::Forward {
            source_unit,
            occurrence,
            ..
        }) = audits.manifests.get(id)
        else {
            continue;
        };
        let LinkTarget::Internal { target } = &occurrence.target else {
            continue;
        };
        let coverage = positives(&coverage_subject(source_unit));
        let targets = positives(&target_subject(&target.key));
        let roles: BTreeSet<_> = coverage
            .iter()
            .filter_map(|review| match &review.audit {
                Some(Assessment::Coverage { links, .. }) => links
                    .iter()
                    .find(|link| link.occurrence == occurrence.id)
                    .map(|link| match link.role {
                        LinkRole::Conceptual => 0,
                        LinkRole::Navigation => 1,
                    }),
                _ => None,
            })
            .collect();
        if coverage.is_empty() || targets.is_empty() {
            continue;
        } // Their missing evidence is separately blocking.
        if roles.len() != 1 {
            errors.push((
                id.clone(),
                "active coverage reviews disagree about this link's conceptual role".into(),
            ));
            continue;
        }
        let role = *roles.first().unwrap();
        let definitions: Vec<_> = targets
            .iter()
            .filter_map(|review| match &review.audit {
                Some(Assessment::Target { definition, .. }) => Some(definition),
                _ => None,
            })
            .collect();
        for review in records
            .iter()
            .filter(|review| review.conclusion == Conclusion::Corresponds)
        {
            let Some(Assessment::Forward { assessment }) = &review.audit else {
                continue;
            };
            let valid = match assessment {
                OrderAssessment::Navigation { .. } => role == 1,
                OrderAssessment::Forward { .. } => {
                    role == 0
                        && !definitions.is_empty()
                        && definitions.iter().all(|definition| {
                            matches!(
                                definition_direction(&audits.links, occurrence, target, definition),
                                Direction::Forward | Direction::Unordered
                            )
                        })
                }
                OrderAssessment::Backward { .. } => {
                    role == 0
                        && !definitions.is_empty()
                        && definitions.iter().all(|definition| {
                            definition_direction(&audits.links, occurrence, target, definition)
                                == Direction::Backward
                        })
                }
            };
            if !valid {
                errors.push((id.clone(), "order disposition disagrees with current coverage or the actual defining occurrence".into()));
            }
        }
    }
    errors
}

fn definition_direction(
    links: &LinkInventory,
    occurrence: &LinkOccurrence,
    target: &Target,
    definition: &DefinitionSpan,
) -> Direction {
    if definition.path == occurrence.source.path {
        if definition.end <= occurrence.source.range.start {
            Direction::Backward
        } else if definition.start >= occurrence.source.range.end {
            Direction::Forward
        } else {
            Direction::Local
        }
    } else {
        let source = links
            .chapters
            .iter()
            .find(|chapter| chapter.path == occurrence.source.path)
            .map(|chapter| chapter.order);
        match (target.chapter_order, source) {
            (Some(target), Some(source)) if target < source => Direction::Backward,
            (Some(target), Some(source)) if target > source => Direction::Forward,
            _ => Direction::Unordered,
        }
    }
}

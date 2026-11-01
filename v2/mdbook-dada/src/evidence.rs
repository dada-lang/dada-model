//! Syntactic evidence validation. This module never invokes an agent or proof checker.
use crate::inventory::{hash, Input, Inventory, SCHEMA};
use crate::units::UnitKind;
use annotate_snippets::{AnnotationKind, Group, Level, Renderer, Snippet};
use anyhow::{ensure, Context, Result};
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::Write,
    path::{Path, PathBuf},
};

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReviewBundle {
    pub schema: u32,
    pub unit: String,
    pub inputs: Vec<Input>,
    pub digest: String,
}

impl ReviewBundle {
    pub fn prepare(inventory: &Inventory, unit: &str, extra: &[String]) -> Result<Self> {
        ensure!(
            inventory.unit(unit)?.kind != UnitKind::FutureNote,
            "future notes have no formalization to review"
        );
        let mut inputs = inventory.inputs(unit)?;
        for path in extra {
            inputs.push(inventory.extra_input(path)?);
        }
        inputs.sort_by(|a, b| a.key.cmp(&b.key));
        let mut bundle = Self {
            schema: SCHEMA,
            unit: unit.to_owned(),
            inputs,
            digest: String::new(),
        };
        bundle.digest = bundle.content_digest()?;
        ensure!(
            bundle.integrity_errors().is_empty(),
            "duplicate inputs in bundle"
        );
        Ok(bundle)
    }

    fn content_digest(&self) -> Result<String> {
        // Locations are retrieval aids, not identity: moving a Markdown block
        // without changing it need not stale a review. Paths and exact content do.
        let identities: Vec<_> = self
            .inputs
            .iter()
            .map(|input| (&input.key, &input.path, &input.sha256))
            .collect();
        Ok(hash(&serde_json::to_vec(&(
            self.schema,
            &self.unit,
            identities,
        ))?))
    }

    fn integrity_errors(&self) -> Vec<String> {
        let mut errors = Vec::new();
        if self.schema != SCHEMA {
            errors.push(format!("unsupported bundle schema {}", self.schema));
        }
        if self.content_digest().ok().as_ref() != Some(&self.digest) {
            errors.push("bundle digest does not match its input manifest".into());
        }
        let mut seen = BTreeSet::new();
        for input in &self.inputs {
            if !seen.insert(&input.key) {
                errors.push(format!("duplicate input {}", input.key));
            }
            if hash(input.content.as_bytes()) != input.sha256 {
                errors.push(format!("snapshot hash does not match {}", input.key));
            }
            if input.line == 0 {
                errors.push(format!("invalid source line for {}", input.key));
            }
        }
        errors
    }
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Conclusion {
    Corresponds,
    Mismatch,
    Inconclusive,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReviewRecord {
    pub schema: u32,
    pub bundle: String,
    pub reviewer: String,
    pub provenance: String,
    pub examined: Vec<String>,
    pub conclusion: Conclusion,
    pub rationale: String,
    pub limitations: Vec<String>,
    #[serde(default)]
    pub supersedes: Vec<String>,
}

impl ReviewRecord {
    pub fn digest(&self) -> Result<String> {
        Ok(hash(&serde_json::to_vec(self)?))
    }
}

/// Compare against the independently derived inventory, not a self-declared
/// checklist. Extra inputs are allowed only as current project file snapshots.
pub fn validate_bundle(inventory: &Inventory, bundle: &ReviewBundle) -> Result<Vec<String>> {
    validate_bundle_against(inventory, bundle, inventory.inputs(&bundle.unit)?)
}

fn validate_bundle_against(
    inventory: &Inventory,
    bundle: &ReviewBundle,
    required: Vec<Input>,
) -> Result<Vec<String>> {
    let mut errors = bundle.integrity_errors();
    let mut expected: BTreeMap<_, _> = required
        .into_iter()
        .map(|input| (input.key.clone(), input))
        .collect();
    for input in &bundle.inputs {
        if let Some(path) = input.key.strip_prefix("extra:") {
            match inventory.extra_input(path) {
                Ok(extra) => {
                    expected.insert(extra.key.clone(), extra);
                }
                Err(error) => errors.push(format!("cannot resolve {}: {error:#}", input.key)),
            }
        }
    }
    let actual: BTreeMap<_, _> = bundle
        .inputs
        .iter()
        .map(|input| (&input.key, input))
        .collect();
    for (key, input) in &expected {
        match actual.get(key) {
            None => errors.push(format!("missing required input {key}")),
            Some(saved)
                if saved.content != input.content
                    || saved.sha256 != input.sha256
                    || saved.path != input.path =>
            {
                errors.push(format!("stale or substituted input {key}"))
            }
            _ => {}
        }
    }
    for key in actual.keys() {
        if !expected.contains_key(*key) {
            errors.push(format!(
                "unexpected input {key}; add consulted files with prepare --input"
            ));
        }
    }
    Ok(errors)
}

pub fn validate_review(bundle: &ReviewBundle, review: &ReviewRecord) -> Vec<String> {
    let mut errors = Vec::new();
    if review.schema != SCHEMA {
        errors.push(format!("unsupported review schema {}", review.schema));
    }
    if review.bundle != bundle.digest {
        errors.push("review names a different bundle".into());
    }
    for (field, value) in [
        ("reviewer", &review.reviewer),
        ("provenance", &review.provenance),
        ("rationale", &review.rationale),
    ] {
        if value.trim().is_empty() {
            errors.push(format!("review requires a nonempty {field}"));
        }
    }
    if review
        .limitations
        .iter()
        .any(|entry| entry.trim().is_empty())
    {
        errors.push("limitations must not contain empty entries".into());
    }
    let examined: BTreeSet<_> = review.examined.iter().collect();
    if examined.len() != review.examined.len() {
        errors.push("duplicate examined input".into());
    }
    for input in &bundle.inputs {
        if input.requires_examination() && !examined.contains(&input.key) {
            errors.push(format!(
                "review did not examine required input {}",
                input.key
            ));
        }
    }
    for key in examined {
        if !bundle.inputs.iter().any(|input| &input.key == key) {
            errors.push(format!("examined input is not in bundle: {key}"));
        }
    }
    let supersedes: BTreeSet<_> = review.supersedes.iter().collect();
    if supersedes.len() != review.supersedes.len() {
        errors.push("duplicate superseded review".into());
    }
    errors
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T> {
    serde_json::from_slice(&fs::read(path).with_context(|| format!("reading {}", path.display()))?)
        .with_context(|| format!("parsing {}", path.display()))
}

pub(crate) fn write_immutable<T: Serialize>(
    root: &Path,
    relative: &Path,
    value: &T,
) -> Result<PathBuf> {
    let path = root.join(relative);
    let parent = path.parent().context("artifact has no parent")?;
    fs::create_dir_all(parent)?;
    ensure!(
        parent.canonicalize()?.starts_with(root),
        "evidence output escapes project"
    );
    let mut bytes = serde_json::to_vec_pretty(value)?;
    bytes.push(b'\n');
    if path.exists() {
        ensure!(
            !fs::symlink_metadata(&path)?.file_type().is_symlink(),
            "evidence output is a symbolic link"
        );
        ensure!(
            fs::read(&path)? == bytes,
            "immutable evidence differs at {}",
            path.display()
        );
    } else {
        fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)?
            .write_all(&bytes)?;
    }
    Ok(path)
}

pub fn save_bundle(inventory: &Inventory, bundle: &ReviewBundle) -> Result<PathBuf> {
    let current = Inventory::load(&inventory.root)?;
    let inventory = &current;
    let errors = validate_bundle(inventory, bundle)?;
    ensure!(
        errors.is_empty(),
        "cannot save bundle: {}",
        errors.join("; ")
    );
    let relative = PathBuf::from("evidence/bundles").join(format!("{}.json", bundle.digest));
    let existing = inventory.root.join(&relative);
    if existing.exists() {
        ensure!(
            existing.canonicalize()?.starts_with(&inventory.root),
            "evidence output escapes project"
        );
        let saved: ReviewBundle = read_json(&existing)?;
        ensure!(
            saved.digest == bundle.digest && validate_bundle(inventory, &saved)?.is_empty(),
            "stored bundle is inconsistent"
        );
        // Same inputs at new source line numbers reuse the original snapshot.
        return Ok(existing);
    }
    write_immutable(&inventory.root, &relative, bundle)
}

/// Record a review only after checking the same current input set used by check.
/// Recording a mismatch is permitted and will cause required review checks to fail.
pub fn record(
    inventory: &Inventory,
    bundle: &ReviewBundle,
    review: &ReviewRecord,
) -> Result<PathBuf> {
    let current = Inventory::load(&inventory.root)?;
    let inventory = &current;
    ensure!(
        inventory.unit(&bundle.unit)?.kind != UnitKind::FutureNote,
        "cannot record correspondence for a future note: it has no formalization"
    );
    let mut errors = validate_bundle(inventory, bundle)?;
    errors.extend(validate_review(bundle, review));
    ensure!(
        errors.is_empty(),
        "cannot record review: {}",
        errors.join("; ")
    );
    ensure!(
        !inventory.unit(&bundle.unit)?.draft,
        "cannot record review for draft unit {}: complete its formalization and matching citations, remove :status: draft, then prepare and review a new bundle",
        bundle.unit
    );
    for previous in &review.supersedes {
        ensure!(valid_digest(previous), "invalid superseded review digest");
        let old: ReviewRecord = read_json(
            &inventory
                .root
                .join("evidence/records")
                .join(&bundle.unit)
                .join(format!("{previous}.json")),
        )?;
        ensure!(
            old.digest()? == *previous,
            "superseded review contents differ"
        );
        let prior: ReviewBundle = read_json(
            &inventory
                .root
                .join("evidence/bundles")
                .join(format!("{}.json", old.bundle)),
        )?;
        ensure!(
            prior.unit == bundle.unit,
            "superseded review must concern the same unit"
        );
    }
    save_bundle(inventory, bundle)?;
    write_immutable(
        &inventory.root,
        &PathBuf::from("evidence/records")
            .join(&bundle.unit)
            .join(format!("{}.json", review.digest()?)),
        review,
    )
}

fn valid_digest(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
}

#[derive(Debug)]
pub struct Issue {
    pub unit: Option<String>,
    pub message: String,
    pub details: Vec<String>,
}

#[derive(Debug)]
pub struct UnitStatus {
    pub unit: String,
    pub evidence: &'static str,
    pub correspondence: &'static str,
}

#[derive(Debug, Default)]
pub struct Report {
    pub statuses: Vec<UnitStatus>,
    pub issues: Vec<Issue>,
}

impl Report {
    pub fn is_ok(&self) -> bool {
        self.issues.is_empty()
    }

    pub fn render(&self, inventory: &Inventory) -> String {
        let mut result = String::new();
        for issue in &self.issues {
            let mut group = Group::with_title(Level::ERROR.primary_title(&issue.message));
            if let Some(unit) = issue.unit.as_ref().and_then(|id| inventory.units.get(id)) {
                let source = &inventory.sources[&unit.source_path];
                // Highlight the header/options, keeping the complete authored body
                // available but avoiding enormous math snippets in diagnostics.
                let header_end = source[unit.range.start..unit.range.end]
                    .find("\n\n")
                    .map_or(unit.range.end, |end| unit.range.start + end);
                group = group.element(
                    Snippet::source(source)
                        .path(&unit.source_path)
                        .fold(true)
                        .annotation(
                            AnnotationKind::Primary
                                .span(unit.range.start..header_end)
                                .label("evidence required for this unit"),
                        ),
                );
            }
            let mut groups = vec![group];
            for detail in issue.details.iter().take(8) {
                groups.push(Group::with_title(Level::NOTE.secondary_title(detail)));
            }
            if let Some(unit) = &issue.unit {
                let help = if inventory.units.get(unit).is_some_and(|unit| unit.draft) {
                    format!("complete the formalization and matching citations for {unit}, remove `:status: draft`, then prepare and review a new bundle")
                } else {
                    format!("run `cargo run -p mdbook-dada --bin dada-spec -- prepare {unit}`, review the packet, then use `dada-spec record <bundle> <review>`")
                };
                groups.push(Group::with_title(Level::HELP.secondary_title(help)));
            }
            groups.push(Group::with_title(Level::HELP.secondary_title("follow md/repo/correspondence-review.md; do not refresh hashes without reviewing changed inputs")));
            result.push_str(&Renderer::plain().render(&groups));
            result.push('\n');
        }
        result
    }
}

/// Shared fallback for failures before a unit inventory can be constructed.
pub fn format_error(error: &anyhow::Error) -> String {
    Renderer::plain().render(&[
        Group::with_title(Level::ERROR.primary_title(format!("{error:#}"))),
        Group::with_title(Level::HELP.secondary_title("repair the reported source or citation, then run `cargo run -p mdbook-dada --bin dada-spec -- check`; see md/repo/correspondence-review.md")),
    ])
}

fn json_files(root: &Path, directory: &Path) -> Result<Vec<PathBuf>> {
    if !directory.exists() {
        return Ok(Vec::new());
    }
    ensure!(
        directory.canonicalize()?.starts_with(root),
        "evidence directory escapes project"
    );
    let mut files = Vec::new();
    for entry in fs::read_dir(directory)? {
        let path = entry?.path();
        ensure!(
            !fs::symlink_metadata(&path)?.file_type().is_symlink(),
            "evidence contains symbolic link {}",
            path.display()
        );
        if path
            .extension()
            .is_some_and(|extension| extension == "json")
        {
            files.push(path);
        }
    }
    files.sort();
    Ok(files)
}

/// Check all required units, including record presence, minimum inputs and freshness.
/// Neither the review's conclusion nor a passing result establishes a Lean proof.
pub fn check(inventory: &Inventory) -> Result<Report> {
    let mut report = Report::default();
    if let Err(error) = crate::mechanical::records(&inventory.root) {
        report.issues.push(Issue {
            unit: None,
            message: "malformed mechanical execution evidence".into(),
            details: vec![format!("{error:#}")],
        });
    }
    let mut bundles = BTreeMap::new();
    for path in json_files(&inventory.root, &inventory.root.join("evidence/bundles"))? {
        match read_json::<ReviewBundle>(&path) {
            Ok(bundle) => {
                let errors = bundle.integrity_errors();
                let name = path
                    .file_stem()
                    .and_then(|name| name.to_str())
                    .unwrap_or("");
                if !errors.is_empty() || name != bundle.digest {
                    report.issues.push(Issue {
                        unit: inventory
                            .units
                            .contains_key(&bundle.unit)
                            .then_some(bundle.unit.clone()),
                        message: format!("invalid evidence bundle {}", path.display()),
                        details: errors,
                    });
                } else {
                    bundles.insert(bundle.digest.clone(), bundle);
                }
            }
            Err(error) => report.issues.push(Issue {
                unit: None,
                message: "malformed evidence bundle".into(),
                details: vec![format!("{error:#}")],
            }),
        }
    }
    for id in &inventory.required {
        // Derive inputs even for drafts: malformed
        // citations never disappear because a formalization is unfinished.
        let required = match inventory.inputs(id) {
            Ok(inputs) => inputs,
            Err(error) => {
                report.issues.push(Issue {
                    unit: Some(id.clone()),
                    message: "cannot resolve required evidence inputs".into(),
                    details: vec![format!("{error:#}")],
                });
                report.statuses.push(UnitStatus {
                    unit: id.clone(),
                    evidence: "invalid sources",
                    correspondence: "not checked",
                });
                continue;
            }
        };
        if inventory.unit(id)?.kind == UnitKind::FutureNote {
            report.statuses.push(UnitStatus {
                unit: id.clone(),
                evidence: "future note",
                correspondence: "not applicable",
            });
            continue;
        }
        if inventory.unit(id)?.draft {
            report.statuses.push(UnitStatus {
                unit: id.clone(),
                evidence: "draft",
                correspondence: "not asserted",
            });
            report.issues.push(Issue {
                unit: Some(id.clone()),
                message: format!("draft unit {id} requires formalization"),
                details: vec![
                    "draft status preserves the unit's semantic kind but cannot count as completed correspondence evidence".into(),
                ],
            });
            continue;
        }
        let mut current = BTreeSet::new();
        let mut stale = Vec::new();
        for bundle in bundles.values().filter(|bundle| &bundle.unit == id) {
            // Historical bundles compare with one independently derived current
            // manifest. Re-reading all sources for each past review made the
            // ordinary evidence test grow with the entire review history.
            let errors = validate_bundle_against(inventory, bundle, required.clone())?;
            if errors.is_empty() {
                current.insert(bundle.digest.clone());
            } else {
                stale.extend(errors);
            }
        }
        let mut records = BTreeMap::new();
        for path in json_files(
            &inventory.root,
            &inventory.root.join("evidence/records").join(id),
        )? {
            let parsed = (|| -> Result<ReviewRecord> {
                let review: ReviewRecord = read_json(&path)?;
                ensure!(
                    path.file_stem().and_then(|name| name.to_str()) == Some(&review.digest()?),
                    "record filename does not match contents"
                );
                let bundle = bundles
                    .get(&review.bundle)
                    .context("record's bundle is missing or malformed")?;
                ensure!(&bundle.unit == id, "record filed under wrong unit");
                let errors = validate_review(bundle, &review);
                ensure!(errors.is_empty(), "invalid review: {}", errors.join("; "));
                Ok(review)
            })();
            match parsed {
                Ok(review) => {
                    records.insert(review.digest()?, review);
                }
                Err(error) => report.issues.push(Issue {
                    unit: Some(id.clone()),
                    message: "malformed correspondence review".into(),
                    details: vec![format!("{error:#}")],
                }),
            }
        }
        let mut superseded = BTreeSet::new();
        for review in records.values() {
            for previous in &review.supersedes {
                if records.contains_key(previous) {
                    superseded.insert(previous.clone());
                } else {
                    report.issues.push(Issue {
                        unit: Some(id.clone()),
                        message: "review supersedes absent or unrelated evidence".into(),
                        details: vec![previous.clone()],
                    });
                }
            }
        }
        let stale_active = records.iter().any(|(digest, review)| {
            !superseded.contains(digest) && !current.contains(&review.bundle)
        });
        let active: Vec<_> = records
            .iter()
            .filter(|(digest, review)| {
                current.contains(&review.bundle) && !superseded.contains(*digest)
            })
            .map(|(_, review)| review)
            .collect();
        let evidence = if stale_active {
            "stale"
        } else if !current.is_empty() {
            "current"
        } else if !stale.is_empty() {
            "stale"
        } else {
            "missing"
        };
        let correspondence = if stale_active {
            "stale decision"
        } else if active.is_empty() {
            "missing"
        } else if active
            .iter()
            .any(|review| review.conclusion == Conclusion::Mismatch)
        {
            "mismatch"
        } else if active
            .iter()
            .any(|review| review.conclusion == Conclusion::Inconclusive)
        {
            "inconclusive"
        } else {
            "corresponds"
        };
        report.statuses.push(UnitStatus {
            unit: id.clone(),
            evidence,
            correspondence,
        });
        if correspondence != "corresponds" {
            let mut details = if evidence == "stale" {
                stale
            } else {
                Vec::new()
            };
            details.sort();
            details.dedup();
            if evidence == "current" && active.is_empty() {
                details.push("preparing a bundle does not record a completed review".into());
            }
            report.issues.push(Issue {
                unit: Some(id.clone()),
                message: format!("{evidence} evidence for {id}: correspondence {correspondence}"),
                details,
            });
        }
    }
    Ok(report)
}

pub fn load_bundle(path: &Path) -> Result<ReviewBundle> {
    read_json(path)
}
pub fn load_review(path: &Path) -> Result<ReviewRecord> {
    read_json(path)
}

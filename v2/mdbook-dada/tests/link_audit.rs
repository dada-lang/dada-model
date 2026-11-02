//! Synthetic evidence attacks; these records assert no review of the real book.
use mdbook_dada::{
    evidence::{self, Conclusion, ReviewBundle, ReviewRecord},
    inventory::{hash, Inventory, SCHEMA},
    link_audit::{
        self, Assessment, DefinitionSpan, LinkAssessment, LinkRole, Manifest, OrderAssessment,
    },
};
use std::{
    collections::BTreeSet,
    fs,
    path::PathBuf,
    sync::atomic::{AtomicUsize, Ordering},
};

const SOURCE: &str = r#"# Fixture

```{definition} alpha
:lean: Fixture:Alpha

Alpha denotes the first thing. Later, [Beta](#claim-beta) supplies its comparison.
```

```{definition} beta
:lean: Fixture:Beta

Beta denotes the second thing. Compare [Alpha](#claim-alpha).
```

```{definition} local
:lean: Fixture:Local

Later in this block, [the local property](#claim-local) is introduced.

Local denotes the local property.
```
"#;

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "dada-link-audits-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        let fixture = Self(path);
        for (path, content) in [
            (
                "spec.json",
                r#"{"schema":1,"chapters":["md/model.md"],"policies":["policy.md"]}"#,
            ),
            (
                "book.toml",
                "[book]\nsrc = \"md\"\n[preprocessor.dada]\nlean-source = \"lean\"\n",
            ),
            ("md/SUMMARY.md", "# Summary\n\n- [Fixture](model.md)\n"),
            ("md/model.md", SOURCE),
            (
                "policy.md",
                "Review concepts, definitions, and reading order.\n",
            ),
            ("Cargo.toml", "[workspace]\nmembers = [\"mdbook-dada\"]\n"),
            ("Cargo.lock", "version = 4\n"),
            (
                "mdbook-dada/Cargo.toml",
                "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\n",
            ),
            ("mdbook-dada/src/lib.rs", "pub fn example() {}\n"),
            (
                "mdbook-dada/tests/tests.rs",
                "#[test] fn example_test() {}\n",
            ),
            (
                "lean/Fixture.lean",
                "abbrev Alpha := Nat\n\nabbrev Beta := Nat\n\nabbrev Local := Nat\n",
            ),
            ("lean/lean-toolchain", "leanprover/lean4:v4.35.0\n"),
            ("lean/lakefile.toml", "name = \"fixture\"\n"),
            ("lean/lake-manifest.json", "{\"packages\":[]}\n"),
        ] {
            fixture.write(path, content);
        }
        fixture
    }
    fn write(&self, path: &str, content: &str) {
        let path = self.0.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, content).unwrap();
    }
    fn inventory(&self) -> Inventory {
        Inventory::load(&self.0).unwrap()
    }
    fn prepare(&self, id: &str) -> ReviewBundle {
        ReviewBundle::prepare(&self.inventory(), id, &[]).unwrap()
    }
    fn ids(&self) -> BTreeSet<String> {
        let inventory = self.inventory();
        inventory
            .required
            .iter()
            .filter(|id| inventory.units[*id].kind != mdbook_dada::units::UnitKind::FutureNote)
            .cloned()
            .chain(link_audit::subjects(&inventory).unwrap())
            .collect()
    }
    fn complete(&self) {
        let inventory = self.inventory();
        for id in self.ids() {
            let bundle = self.prepare(&id);
            evidence::record(&inventory, &bundle, &synthetic_review(&bundle)).unwrap();
        }
    }
    fn candidate(&self, unit: &str) -> String {
        link_audit::AuditInventory::build(&self.inventory())
            .unwrap()
            .manifests
            .into_iter()
            .find_map(|(id, manifest)| match manifest {
                Manifest::Forward { source_unit, .. } if source_unit == unit => Some(id),
                _ => None,
            })
            .unwrap()
    }
    fn save_replacement(&self, id: &str, mut review: ReviewRecord) {
        let bundle = self.prepare(id);
        let old = synthetic_review(&bundle);
        review.supersedes = vec![old.digest().unwrap()];
        evidence::record(&self.inventory(), &bundle, &review).unwrap();
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

fn definition(bundle: &ReviewBundle, location: &mdbook_dada::links::Location) -> DefinitionSpan {
    let chapter = &bundle
        .inputs
        .iter()
        .find(|input| input.key == format!("context:link-chapter:{}", location.path))
        .unwrap()
        .content;
    let scope = &chapter[location.range.clone()];
    let start = location.range.start
        + ["Alpha denotes", "Beta denotes", "Local denotes"]
            .into_iter()
            .find_map(|text| scope.find(text))
            .unwrap();
    let end = start + chapter[start..].find('.').unwrap() + 1;
    DefinitionSpan {
        path: location.path.clone(),
        start,
        end,
    }
}

fn synthetic_review(bundle: &ReviewBundle) -> ReviewRecord {
    let audit = if link_audit::is_subject(&bundle.unit) {
        Some(match link_audit::manifest(bundle).unwrap() {
            Manifest::Coverage { source } => Assessment::Coverage {
                prose: "Synthetic fixture assessment of concept coverage in prose.".into(),
                mathematics: "This synthetic fixture contains no mathematics.".into(),
                links: source
                    .occurrences
                    .into_iter()
                    .map(|link| LinkAssessment {
                        occurrence: link.id,
                        role: LinkRole::Conceptual,
                        rationale: "Synthetic reference to the named concept.".into(),
                    })
                    .collect(),
            },
            Manifest::Target { target } => Assessment::Target {
                subject: target.key.clone(),
                definition: definition(bundle, &target.location),
                clarity: "Synthetic defining sentence is identifiable at the target.".into(),
                independence: "Synthetic definition is separated from other subjects.".into(),
            },
            Manifest::Forward { source, .. } => {
                let chapter = &bundle
                    .inputs
                    .iter()
                    .find(|input| input.key == format!("context:link-chapter:{}", source.path))
                    .unwrap()
                    .content;
                let start =
                    source.range.start + chapter[source.range.clone()].find("Later").unwrap();
                Assessment::Forward { assessment: OrderAssessment::Forward {
                    necessity: "Synthetic exception considers moving the definition, use, and splitting the explanation.".into(),
                    signposting: "The source explicitly says Later and links to the definition.".into(),
                    signpost: DefinitionSpan { path: source.path, start, end: start + 5 },
                    minimal_use: "The motivating use assumes only the named comparison, not its defining rules.".into(),
                } }
            }
        })
    } else {
        None
    };
    ReviewRecord {
        schema: SCHEMA,
        bundle: bundle.digest.clone(),
        reviewer: "synthetic test".into(),
        provenance: "Fixture for deterministic validation, not a review of actual prose.".into(),
        examined: bundle
            .inputs
            .iter()
            .filter(|input| input.requires_examination())
            .map(|input| input.key.clone())
            .collect(),
        conclusion: Conclusion::Corresponds,
        rationale: "Synthetic fixture judgment.".into(),
        limitations: vec!["Not evidence for the real book.".into()],
        supersedes: vec![],
        audit,
    }
}

#[test]
fn complete_link_audits_pass_but_preparation_alone_does_not() {
    let fixture = Fixture::new();
    for id in fixture.ids() {
        evidence::save_bundle(&fixture.inventory(), &fixture.prepare(&id)).unwrap();
    }
    let report = evidence::check(&fixture.inventory()).unwrap();
    assert!(!report.is_ok());
    assert!(report
        .issues
        .iter()
        .any(|issue| issue.unit.as_deref() == Some("links.coverage/alpha")));
    fixture.complete();
    let report = evidence::check(&fixture.inventory()).unwrap();
    assert!(report.is_ok(), "{}", report.render(&fixture.inventory()));
}

#[test]
fn coverage_requires_each_occurrence_once_and_both_prose_and_math_rationales() {
    let fixture = Fixture::new();
    let bundle = fixture.prepare("links.coverage/alpha");
    for mutation in 0..4 {
        let mut review = synthetic_review(&bundle);
        if let Some(Assessment::Coverage {
            prose,
            mathematics,
            links,
        }) = &mut review.audit
        {
            match mutation {
                0 => links.clear(),
                1 => links.push(links[0].clone()),
                2 => prose.clear(),
                _ => mathematics.clear(),
            }
        }
        assert!(!evidence::validate_review(&bundle, &review).is_empty());
    }
    let mut review = synthetic_review(&bundle);
    review.audit = None;
    assert!(!evidence::validate_review(&bundle, &review).is_empty());
}

#[test]
fn target_spans_cannot_escape_or_select_empty_text() {
    let fixture = Fixture::new();
    let bundle = fixture.prepare(&link_audit::target_subject("md/model.md#claim-beta"));
    for mutation in 0..4 {
        let mut review = synthetic_review(&bundle);
        if let Some(Assessment::Target {
            definition,
            clarity,
            ..
        }) = &mut review.audit
        {
            match mutation {
                0 => definition.path = "md/other.md".into(),
                1 => definition.start = 0,
                2 => definition.end = definition.start,
                _ => clarity.clear(),
            }
        }
        assert!(!evidence::validate_review(&bundle, &review).is_empty());
    }
    fixture.write(
        "md/model.md",
        &SOURCE.replace("Beta denotes", "Beta α denotes"),
    );
    let bundle = fixture.prepare(&link_audit::target_subject("md/model.md#claim-beta"));
    let mut review = synthetic_review(&fixture.prepare("links.coverage/alpha"));
    let chapter = &bundle
        .inputs
        .iter()
        .find(|input| input.key == "context:link-chapter:md/model.md")
        .unwrap()
        .content;
    let offset = chapter.find('α').unwrap();
    review.bundle = bundle.digest.clone();
    review.examined = bundle
        .inputs
        .iter()
        .filter(|input| input.requires_examination())
        .map(|input| input.key.clone())
        .collect();
    review.audit = Some(Assessment::Target {
        subject: "Beta".into(),
        definition: DefinitionSpan {
            path: "md/model.md".into(),
            start: offset + 1,
            end: offset + 2,
        },
        clarity: "Synthetic clarity.".into(),
        independence: "Synthetic independence.".into(),
    });
    assert!(evidence::validate_review(&bundle, &review)
        .iter()
        .any(|error| error.contains("UTF-8")));
}

#[test]
fn required_audit_source_target_and_order_inputs_cannot_be_removed_by_rehashing() {
    let fixture = Fixture::new();
    let bundle = fixture.prepare("links.coverage/alpha");
    for prefix in [
        "audit:unit:alpha",
        "audit:target:",
        "audit:reading-order",
        "context:link-summary",
    ] {
        let mut reduced = bundle.clone();
        let original = reduced.inputs.len();
        reduced
            .inputs
            .retain(|input| !input.key.starts_with(prefix));
        assert!(reduced.inputs.len() < original);
        let identities: Vec<_> = reduced
            .inputs
            .iter()
            .map(|input| (&input.key, &input.path, &input.sha256))
            .collect();
        reduced.digest =
            hash(&serde_json::to_vec(&(reduced.schema, &reduced.unit, identities)).unwrap());
        assert!(evidence::validate_bundle(&fixture.inventory(), &reduced)
            .unwrap()
            .iter()
            .any(|error| error.starts_with("missing required input")));
    }
}

#[test]
fn an_independent_affirmative_audit_cannot_hide_a_negative_decision() {
    let fixture = Fixture::new();
    fixture.complete();
    let id = link_audit::target_subject("md/model.md#claim-beta");
    let bundle = fixture.prepare(&id);
    let mut negative = synthetic_review(&bundle);
    negative.conclusion = Conclusion::Mismatch;
    negative.rationale = "Synthetic reviewer found a buried definition.".into();
    evidence::record(&fixture.inventory(), &bundle, &negative).unwrap();
    let report = evidence::check(&fixture.inventory()).unwrap();
    assert!(report
        .statuses
        .iter()
        .any(|status| status.unit == id && status.correspondence == "mismatch"));
}

#[test]
fn forward_exceptions_require_all_three_reasons_and_a_real_source_span() {
    let fixture = Fixture::new();
    let bundle = fixture.prepare(&fixture.candidate("alpha"));
    for mutation in 0..4 {
        let mut review = synthetic_review(&bundle);
        if let Some(Assessment::Forward {
            assessment:
                OrderAssessment::Forward {
                    necessity,
                    signposting,
                    signpost,
                    minimal_use,
                },
        }) = &mut review.audit
        {
            match mutation {
                0 => necessity.clear(),
                1 => signposting.clear(),
                2 => minimal_use.clear(),
                _ => signpost.start = 0,
            }
        }
        assert!(!evidence::validate_review(&bundle, &review).is_empty());
    }
}

#[test]
fn a_local_link_before_its_actual_definition_cannot_be_called_backward() {
    let fixture = Fixture::new();
    fixture.complete();
    let id = fixture.candidate("local");
    let bundle = fixture.prepare(&id);
    let mut review = synthetic_review(&bundle);
    review.audit = Some(Assessment::Forward {
        assessment: OrderAssessment::Backward {
            rationale: "The block anchor is earlier; this is insufficient.".into(),
        },
    });
    fixture.save_replacement(&id, review);
    let report = evidence::check(&fixture.inventory()).unwrap();
    assert!(report
        .issues
        .iter()
        .any(|issue| issue.message.contains("actual defining occurrence")));
}

#[test]
fn navigation_exemption_must_agree_with_current_coverage() {
    let fixture = Fixture::new();
    fixture.complete();
    let id = fixture.candidate("alpha");
    let bundle = fixture.prepare(&id);
    let mut review = synthetic_review(&bundle);
    review.audit = Some(Assessment::Forward {
        assessment: OrderAssessment::Navigation {
            rationale: "Synthetic navigation classification.".into(),
        },
    });
    fixture.save_replacement(&id, review);
    assert!(!evidence::check(&fixture.inventory()).unwrap().is_ok());
    let coverage_id = "links.coverage/alpha";
    let mut coverage = synthetic_review(&fixture.prepare(coverage_id));
    if let Some(Assessment::Coverage { links, .. }) = &mut coverage.audit {
        links[0].role = LinkRole::Navigation;
    }
    fixture.save_replacement(coverage_id, coverage);
    let report = evidence::check(&fixture.inventory()).unwrap();
    assert!(report.is_ok(), "{}", report.render(&fixture.inventory()));
}

#[test]
fn independent_positive_reviews_cannot_disagree_on_backward_links_or_target_spans() {
    let fixture = Fixture::new();
    fixture.complete();
    let bundle = fixture.prepare("links.coverage/beta");
    let mut conflict = synthetic_review(&bundle);
    if let Some(Assessment::Coverage { links, .. }) = &mut conflict.audit {
        links[0].role = LinkRole::Navigation;
    }
    evidence::record(&fixture.inventory(), &bundle, &conflict).unwrap();
    let report = evidence::check(&fixture.inventory()).unwrap();
    assert!(report
        .issues
        .iter()
        .any(|issue| issue.message.contains("coverage reviews disagree")));
    let bundle = fixture.prepare(&link_audit::target_subject("md/model.md#claim-alpha"));
    let mut conflict = synthetic_review(&bundle);
    if let Some(Assessment::Target { definition, .. }) = &mut conflict.audit {
        definition.end -= 1;
    }
    evidence::record(&fixture.inventory(), &bundle, &conflict).unwrap();
    let report = evidence::check(&fixture.inventory()).unwrap();
    assert!(report
        .issues
        .iter()
        .any(|issue| issue.message.contains("target reviews disagree")));
}

#[test]
fn source_movement_summary_order_and_reference_definitions_invalidate_inputs() {
    let fixture = Fixture::new();
    let bundle = fixture.prepare("links.coverage/alpha");
    fixture.write("md/model.md", &format!("\n{SOURCE}"));
    assert!(!evidence::validate_bundle(&fixture.inventory(), &bundle)
        .unwrap()
        .is_empty());
    fixture.write("md/model.md", SOURCE);
    fixture.write("md/other.md", "# Other\n");
    fixture.write(
        "md/SUMMARY.md",
        "# Summary\n\n- [Other](other.md)\n- [Fixture](model.md)\n",
    );
    assert!(!evidence::validate_bundle(&fixture.inventory(), &bundle)
        .unwrap()
        .is_empty());
    fixture.write(
        "md/model.md",
        &SOURCE
            .replace("[Beta](#claim-beta)", "[Beta][beta-ref]")
            .replace(
                "Beta denotes the second thing.",
                "Beta denotes the second thing.\n\n[beta-ref]: #claim-beta\n",
            ),
    );
    let bundle = fixture.prepare("links.coverage/alpha");
    let changed = fs::read_to_string(fixture.0.join("md/model.md"))
        .unwrap()
        .replace("[beta-ref]: #claim-beta", "[beta-ref]: #claim-alpha");
    fixture.write("md/model.md", &changed);
    assert!(!evidence::validate_bundle(&fixture.inventory(), &bundle)
        .unwrap()
        .is_empty());
}

#[test]
fn historical_correspondence_record_digest_is_unchanged_without_audit_field() {
    let fixture = Fixture::new();
    let review = synthetic_review(&fixture.prepare("alpha"));
    let value = serde_json::to_value(&review).unwrap();
    assert!(value.get("audit").is_none());
    let old = serde_json::json!({
        "schema": review.schema, "bundle": review.bundle, "reviewer": review.reviewer,
        "provenance": review.provenance, "examined": review.examined, "conclusion": review.conclusion,
        "rationale": review.rationale, "limitations": review.limitations, "supersedes": review.supersedes,
    });
    let parsed: ReviewRecord = serde_json::from_value(old).unwrap();
    assert_eq!(parsed.digest().unwrap(), review.digest().unwrap());
    // Verify exact historical field order rather than serde_json::Value's map order.
    let old_bytes = format!("{{\"schema\":{},\"bundle\":{},\"reviewer\":{},\"provenance\":{},\"examined\":{},\"conclusion\":{},\"rationale\":{},\"limitations\":{},\"supersedes\":{}}}",
        review.schema, serde_json::to_string(&review.bundle).unwrap(), serde_json::to_string(&review.reviewer).unwrap(), serde_json::to_string(&review.provenance).unwrap(), serde_json::to_string(&review.examined).unwrap(), serde_json::to_string(&review.conclusion).unwrap(), serde_json::to_string(&review.rationale).unwrap(), serde_json::to_string(&review.limitations).unwrap(), serde_json::to_string(&review.supersedes).unwrap());
    assert_eq!(hash(old_bytes.as_bytes()), review.digest().unwrap());
}

#[test]
fn malformed_retired_audit_records_are_still_validated() {
    let fixture = Fixture::new();
    fixture.complete();
    let retired = fixture.candidate("alpha");
    let bundle = fixture.prepare(&retired);
    let record = synthetic_review(&bundle);
    fixture.write(
        "md/model.md",
        &SOURCE.replace("Later, [Beta](#claim-beta) supplies its comparison.", ""),
    );
    fixture.write(
        &format!(
            "evidence/records/{retired}/{}.json",
            record.digest().unwrap()
        ),
        "{}",
    );
    let report = evidence::check(&fixture.inventory()).unwrap();
    assert!(report
        .issues
        .iter()
        .any(|issue| issue.message == "malformed stored review"));
}

#[test]
fn draft_link_audits_can_be_recorded_and_invalid_subjects_cannot_escape_the_inventory() {
    let fixture = Fixture::new();
    fixture.write(
        "md/model.md",
        &SOURCE.replace(":lean: Fixture:Alpha", ":status: draft"),
    );
    let bundle = fixture.prepare("links.coverage/alpha");
    evidence::record(&fixture.inventory(), &bundle, &synthetic_review(&bundle)).unwrap();
    for id in [
        "links.coverage/absent",
        "links.coverage/../../outside",
        "links.unrecognized/alpha",
    ] {
        assert!(ReviewBundle::prepare(&fixture.inventory(), id, &[]).is_err());
    }
}

#[test]
fn future_notes_require_editorial_audits_without_claiming_correspondence() {
    let fixture = Fixture::new();
    fixture.write("md/model.md", &SOURCE.replace("# Fixture\n", "# Fixture\n\n```{future-note} future.one\n\nLater, [Beta](#claim-beta) supplies an idea to explore.\n```\n"));
    let inventory = fixture.inventory();
    let audits = link_audit::AuditInventory::build(&inventory).unwrap();
    assert!(audits.manifests.contains_key("links.coverage/future.one"));
    assert!(audits.manifests.values().any(|manifest| matches!(manifest, Manifest::Forward { source_unit, .. } if source_unit == "future.one")));
    assert!(ReviewBundle::prepare(&inventory, "future.one", &[]).is_err());
    fixture.complete();
    let report = evidence::check(&fixture.inventory()).unwrap();
    assert!(report.is_ok(), "{}", report.render(&fixture.inventory()));
    assert!(report
        .statuses
        .iter()
        .any(|status| status.unit == "future.one" && status.correspondence == "not applicable"));
    assert!(report
        .statuses
        .iter()
        .any(|status| status.unit == "links.coverage/future.one"
            && status.correspondence == "corresponds"));
}

#[test]
fn conceptual_external_links_require_an_inspectable_local_definition() {
    let fixture = Fixture::new();
    fixture.write(
        "md/model.md",
        &SOURCE.replace(
            "[Beta](#claim-beta)",
            "[Beta](https://example.invalid/beta)",
        ),
    );
    let bundle = fixture.prepare("links.coverage/alpha");
    let mut review = synthetic_review(&bundle);
    assert!(evidence::validate_review(&bundle, &review)
        .iter()
        .any(|error| error.contains("local, snapshotted")));
    review.conclusion = Conclusion::Mismatch;
    assert!(evidence::validate_review(&bundle, &review).is_empty());
}

//! Independent attacks on the evidence boundary, using complete project fixtures.
use mdbook_dada::{
    evidence::{self, Conclusion, ReviewBundle, ReviewRecord},
    inventory::{hash, Inventory, SCHEMA},
};
use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicUsize, Ordering},
};

const MODEL: &str = r#"# A small model

```{definition} model.variable
:lean: Fixture:Variable

A runtime variable is identified by a natural number.
```

```{definition} model.empty
:lean: Fixture:empty
:uses: model.variable

The empty list has no variables: \\(V = []\\).
```
"#;

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let root = std::env::temp_dir().join(format!(
            "dada-evidence-tests-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).unwrap();
        let fixture = Self(root);
        fixture.write("spec.json", r#"{"schema":1,"chapters":["md/model.md"],"policies":["policy.md"],"context":["context.txt"]}"#);
        fixture.write(
            "book.toml",
            "[book]\nsrc = \"md\"\n[preprocessor.dada]\nlean-source = \"lean\"\n",
        );
        fixture.write("md/model.md", MODEL);
        fixture.write(
            "policy.md",
            "Compare the whole statement with each exact declaration.\n",
        );
        fixture.write(
            "context.txt",
            "The natural-number variable model is the common context.\n",
        );
        fixture.write("Cargo.toml", "[workspace]\nmembers = [\"mdbook-dada\"]\n");
        fixture.write("Cargo.lock", "version = 4\n");
        fixture.write(
            "mdbook-dada/Cargo.toml",
            "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\n",
        );
        fixture.write("mdbook-dada/src/lib.rs", "pub fn validate() {}\n");
        fixture.write("mdbook-dada/tests/basic.rs", "#[test]\nfn checked() {}\n");
        fixture.write("lean/Fixture.lean", "abbrev Variable := Nat\n\ndef empty : List Variable := []\n\ndef other : List Variable := [1]\n");
        fixture.write("lean/lean-toolchain", "leanprover/lean4:v4.35.0\n");
        fixture.write("lean/lakefile.toml", "name = \"fixture\"\n");
        fixture.write("lean/lake-manifest.json", "{\"packages\":[]}\n");
        fixture
    }

    fn write(&self, path: &str, source: &str) {
        let path = self.0.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, source).unwrap();
    }

    fn inventory(&self) -> Inventory {
        Inventory::load(&self.0).unwrap()
    }

    fn bundle(&self) -> ReviewBundle {
        ReviewBundle::prepare(&self.inventory(), "model.empty", &[]).unwrap()
    }

    fn complete_reviews(&self) {
        let inventory = self.inventory();
        for id in &inventory.required {
            let bundle = ReviewBundle::prepare(&inventory, id, &[]).unwrap();
            evidence::record(&inventory, &bundle, &review(&bundle)).unwrap();
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

fn review(bundle: &ReviewBundle) -> ReviewRecord {
    ReviewRecord {
        schema: SCHEMA,
        bundle: bundle.digest.clone(),
        reviewer: "synthetic integration-test reviewer".into(),
        provenance: "Fixture data exercising validation, not a real correspondence review.".into(),
        examined: bundle
            .inputs
            .iter()
            .filter(|input| input.requires_examination())
            .map(|input| input.key.clone())
            .collect(),
        conclusion: Conclusion::Corresponds,
        rationale: "Fixture approval used to test the syntactic record lifecycle.".into(),
        limitations: vec!["This fixture record establishes no semantic claim.".into()],
        supersedes: vec![],
    }
}

// Model an attacker who repackages a reduced/altered manifest with internally
// consistent hashes. Required inputs must come from current sources, not these
// self-consistent checksums. This helper is deliberately independent of private
// production validation and never manufactures repository review evidence.
fn repack(bundle: &mut ReviewBundle) {
    let identities: Vec<_> = bundle
        .inputs
        .iter()
        .map(|input| (&input.key, &input.path, &input.sha256))
        .collect();
    bundle.digest = hash(&serde_json::to_vec(&(bundle.schema, &bundle.unit, identities)).unwrap());
}

#[test]
fn complete_current_reviews_pass_and_remain_distinct_from_mechanical_checks() {
    let fixture = Fixture::new();
    fixture.complete_reviews();
    let inventory = fixture.inventory();
    let report = evidence::check(&inventory).unwrap();
    assert!(report.is_ok(), "{}", report.render(&inventory));
    assert_eq!(report.statuses.len(), 2);
    for status in &report.statuses {
        assert_eq!(status.evidence, "current");
        assert_eq!(status.correspondence, "corresponds");
        assert_eq!(status.mechanical, "not recorded");
    }
}

#[test]
fn rejects_missing_or_substituted_required_inputs() {
    let fixture = Fixture::new();
    let inventory = fixture.inventory();
    let original = fixture.bundle();
    assert!(original
        .inputs
        .iter()
        .any(|input| input.key == "context:lean/Fixture.lean"));
    for key in [
        "unit:model.empty",
        "lean:Fixture:empty",
        "unit:model.variable",
        "lean:Fixture:Variable",
        "policy:policy.md",
        "context:context.txt",
        "tool:Cargo.lock",
        "context:lean/lean-toolchain",
    ] {
        let mut reduced = original.clone();
        reduced.inputs.retain(|input| input.key != key);
        repack(&mut reduced);
        let errors = evidence::validate_bundle(&inventory, &reduced).unwrap();
        assert!(
            errors
                .iter()
                .any(|error| error == &format!("missing required input {key}")),
            "missing {key} escaped validation: {errors:?}"
        );
        assert!(
            !errors.iter().any(|error| error.contains("digest")),
            "attack manifest should remain internally consistent"
        );
    }

    let mut substituted = original;
    let input = substituted
        .inputs
        .iter_mut()
        .find(|input| input.key == "lean:Fixture:empty")
        .unwrap();
    input.content = "def other : List Variable := [1]".into();
    input.sha256 = hash(input.content.as_bytes());
    repack(&mut substituted);
    let errors = evidence::validate_bundle(&inventory, &substituted).unwrap();
    assert!(
        errors
            .iter()
            .any(|error| error == "stale or substituted input lean:Fixture:empty"),
        "{errors:?}"
    );
}

#[test]
fn snapshot_and_manifest_tampering_are_rejected() {
    let fixture = Fixture::new();
    let inventory = fixture.inventory();
    let original = fixture.bundle();
    let mut snapshot = original.clone();
    snapshot.inputs[0].content.push_str("\nforged snapshot");
    let errors = evidence::validate_bundle(&inventory, &snapshot).unwrap();
    assert!(
        errors.iter().any(|error| error.contains("snapshot hash")),
        "{errors:?}"
    );
    let mut manifest = original;
    manifest.digest = "0".repeat(64);
    assert!(evidence::validate_bundle(&inventory, &manifest)
        .unwrap()
        .iter()
        .any(|error| error.contains("bundle digest")));
}

#[test]
fn authored_and_formal_source_changes_stale_existing_reviews() {
    for (path, replacement, key) in [
        (
            "md/model.md",
            MODEL.replace("has no variables", "has one variable"),
            "unit:model.empty",
        ),
        (
            "lean/Fixture.lean",
            "abbrev Variable := Nat\n\ndef empty : List Variable := [1]\n".into(),
            "lean:Fixture:empty",
        ),
        (
            "policy.md",
            "A different review policy.\n".into(),
            "policy:policy.md",
        ),
        (
            "mdbook-dada/src/lib.rs",
            "pub fn validate() { /* changed */ }\n".into(),
            "tool:mdbook-dada/src/lib.rs",
        ),
    ] {
        let fixture = Fixture::new();
        fixture.complete_reviews();
        let bundle = fixture.bundle();
        fixture.write(path, &replacement);
        let inventory = fixture.inventory();
        assert!(evidence::record(&inventory, &bundle, &review(&bundle)).is_err());
        let report = evidence::check(&inventory).unwrap();
        assert!(!report.is_ok());
        let message = report.render(&inventory);
        assert!(message.contains(key), "missing {key}: {message}");
        assert!(
            message.contains("md/model.md:"),
            "missing source location: {message}"
        );
        assert!(message.contains("help:"), "missing help: {message}");
        assert!(
            message.contains("prepare model.empty"),
            "missing preparation command: {message}"
        );
        assert!(
            message.contains("correspondence-review.md"),
            "missing reviewer instructions: {message}"
        );
    }
}

#[test]
fn renderer_lean_fixtures_are_required_freshness_inputs() {
    let fixture = Fixture::new();
    let path = "mdbook-dada/tests/fixtures/lean/Renderer.lean";
    let key = format!("tool:{path}");
    fixture.write(path, "abbrev Sample := Nat\n");
    fixture.complete_reviews();
    let bundle = fixture.bundle();
    let input = bundle.inputs.iter().find(|input| input.key == key).unwrap();
    assert_eq!(input.content, "abbrev Sample := Nat\n");

    let mut reduced = bundle.clone();
    reduced.inputs.retain(|input| input.key != key);
    repack(&mut reduced);
    let errors = evidence::validate_bundle(&fixture.inventory(), &reduced).unwrap();
    assert!(errors.contains(&format!("missing required input {key}")));

    fixture.write(path, "abbrev Sample := String\n");
    let inventory = fixture.inventory();
    assert!(evidence::record(&inventory, &bundle, &review(&bundle)).is_err());
    let report = evidence::check(&inventory).unwrap();
    assert!(!report.is_ok());
    assert!(report.render(&inventory).contains(&key));
}

#[test]
fn recording_rechecks_sources_even_with_an_existing_inventory() {
    let fixture = Fixture::new();
    let inventory = fixture.inventory();
    let bundle = ReviewBundle::prepare(&inventory, "model.empty", &[]).unwrap();
    fixture.write(
        "md/model.md",
        &MODEL.replace("has no variables", "has one variable"),
    );
    assert!(
        evidence::record(&inventory, &bundle, &review(&bundle)).is_err(),
        "record accepted a changed authored source through a cached inventory"
    );
}

#[test]
fn moving_a_unit_without_changing_its_contents_preserves_review() {
    let fixture = Fixture::new();
    fixture.complete_reviews();
    let old_bundle = fixture.bundle();
    fixture.write("md/model.md", &format!("\n\n{MODEL}"));
    let inventory = fixture.inventory();
    let new_bundle = ReviewBundle::prepare(&inventory, "model.empty", &[]).unwrap();
    assert_eq!(old_bundle.digest, new_bundle.digest);
    assert!(evidence::validate_bundle(&inventory, &old_bundle)
        .unwrap()
        .is_empty());
    let report = evidence::check(&inventory).unwrap();
    assert!(report.is_ok(), "{}", report.render(&inventory));
    evidence::save_bundle(&inventory, &new_bundle)
        .expect("preparing the same content at a new source line must remain idempotent");
}

#[test]
fn prepared_bundles_are_not_completed_reviews() {
    let fixture = Fixture::new();
    let inventory = fixture.inventory();
    let bundle = fixture.bundle();
    evidence::save_bundle(&inventory, &bundle).unwrap();
    let report = evidence::check(&inventory).unwrap();
    assert!(!report.is_ok());
    let status = report
        .statuses
        .iter()
        .find(|status| status.unit == "model.empty")
        .unwrap();
    assert_eq!(status.evidence, "current");
    assert_eq!(status.correspondence, "missing");
    assert!(report
        .render(&inventory)
        .contains("preparing a bundle does not record a completed review"));
}

#[test]
fn review_must_examine_exact_citations_and_provide_a_rationale() {
    let fixture = Fixture::new();
    let bundle = fixture.bundle();
    let mut incomplete = review(&bundle);
    incomplete
        .examined
        .retain(|key| key != "lean:Fixture:empty");
    let errors = evidence::validate_review(&bundle, &incomplete);
    assert!(errors
        .iter()
        .any(|error| error.contains("did not examine required input lean:Fixture:empty")));
    assert!(evidence::record(&fixture.inventory(), &bundle, &incomplete).is_err());
    let mut vague = review(&bundle);
    vague.rationale = " \n ".into();
    assert!(evidence::validate_review(&bundle, &vague)
        .iter()
        .any(|error| error.contains("nonempty rationale")));
    let mut invented = review(&bundle);
    invented.examined.push("lean:Unseen:claim".into());
    assert!(evidence::validate_review(&bundle, &invented)
        .iter()
        .any(|error| error.contains("not in bundle")));
}

#[test]
fn mismatch_and_inconclusive_reviews_never_count_as_correspondence() {
    for conclusion in [Conclusion::Mismatch, Conclusion::Inconclusive] {
        let fixture = Fixture::new();
        fixture.complete_reviews();
        let inventory = fixture.inventory();
        let bundle = fixture.bundle();
        let mut negative = review(&bundle);
        negative.conclusion = conclusion;
        evidence::record(&inventory, &bundle, &negative).unwrap();
        let report = evidence::check(&inventory).unwrap();
        assert!(
            !report.is_ok(),
            "negative review was hidden by a positive one"
        );
        let status = report
            .statuses
            .iter()
            .find(|status| status.unit == "model.empty")
            .unwrap();
        assert_ne!(status.correspondence, "corresponds");
    }
}

#[test]
fn additional_consulted_inputs_are_examined_and_invalidated_on_change() {
    let fixture = Fixture::new();
    fixture.write(
        "notes.txt",
        "Extra assumptions consulted by the reviewer.\n",
    );
    let inventory = fixture.inventory();
    let bundle = ReviewBundle::prepare(&inventory, "model.empty", &["notes.txt".into()]).unwrap();
    let mut incomplete = review(&bundle);
    incomplete.examined.retain(|key| key != "extra:notes.txt");
    assert!(!evidence::validate_review(&bundle, &incomplete).is_empty());
    evidence::record(&inventory, &bundle, &review(&bundle)).unwrap();
    fixture.write("notes.txt", "Changed assumptions.\n");
    let errors = evidence::validate_bundle(&fixture.inventory(), &bundle).unwrap();
    assert!(errors
        .iter()
        .any(|error| error == "stale or substituted input extra:notes.txt"));
    assert!(ReviewBundle::prepare(
        &fixture.inventory(),
        "model.empty",
        &["../outside.txt".into()]
    )
    .is_err());
    assert!(ReviewBundle::prepare(
        &fixture.inventory(),
        "model.empty",
        &["evidence/bundles/anything.json".into()]
    )
    .is_err());
}

#[test]
fn malformed_and_rewritten_records_are_reported() {
    let fixture = Fixture::new();
    fixture.complete_reviews();
    let inventory = fixture.inventory();
    let bundle = fixture.bundle();
    let saved = evidence::record(&inventory, &bundle, &review(&bundle)).unwrap();
    for corrupted in ["{not json}".to_owned(), {
        let mut value = serde_json::to_value(review(&bundle)).unwrap();
        value["rationale"] = "Changed after review".into();
        serde_json::to_string(&value).unwrap()
    }] {
        fs::write(&saved, corrupted).unwrap();
        let report = evidence::check(&inventory).unwrap();
        assert!(!report.is_ok());
        assert!(report
            .render(&inventory)
            .contains("malformed correspondence review"));
    }
}

#[test]
fn rust_test_citations_require_the_named_test_function_itself() {
    let fixture = Fixture::new();
    fixture.write(
        "mdbook-dada/tests/kinds.rs",
        r##"fn plain() {}
fn comment_decoy() { /* #[test] */ }
fn string_decoy() { let _ = "#[test]"; }
mod group { #[test] fn actual() {} }
struct Store;
impl Store { #[test] fn method() {} }
"##,
    );
    for name in [
        "plain",
        "comment_decoy",
        "string_decoy",
        "group",
        "Store::method",
    ] {
        fixture.write("md/meta.md", &format!("```{{definition}} meta.check\n:rust: mdbook-dada/src/lib.rs:validate\n:tests: mdbook-dada/tests/kinds.rs:{name}\n\nValidation rejects missing inputs.\n```\n"));
        assert!(
            fixture.inventory().inputs("meta.check").is_err(),
            "accepted non-test citation {name}"
        );
    }
    fixture.write("md/meta.md", "```{definition} meta.check\n:rust: mdbook-dada/src/lib.rs:validate\n:tests: mdbook-dada/tests/kinds.rs:group::actual\n\nValidation rejects missing inputs.\n```\n");
    let inputs = fixture.inventory().inputs("meta.check").unwrap();
    let selected = inputs
        .iter()
        .find(|input| input.key == "test:mdbook-dada/tests/kinds.rs:group::actual")
        .unwrap();
    assert_eq!(selected.content, "#[test] fn actual() {}");
}

#[test]
fn revised_review_can_supersede_same_unit_after_consulting_more_context() {
    let fixture = Fixture::new();
    fixture.complete_reviews();
    let inventory = fixture.inventory();
    let initial = fixture.bundle();
    let mut unresolved = review(&initial);
    unresolved.conclusion = Conclusion::Inconclusive;
    unresolved.rationale = "Fixture review requests additional context before deciding.".into();
    let old_path = evidence::record(&inventory, &initial, &unresolved).unwrap();
    let old_bytes = fs::read(&old_path).unwrap();
    assert!(!evidence::check(&inventory).unwrap().is_ok());

    fixture.write(
        "additional-context.txt",
        "Additional context resolves the fixture question.\n",
    );
    let revised = ReviewBundle::prepare(
        &inventory,
        "model.empty",
        &["additional-context.txt".into()],
    )
    .unwrap();
    assert_ne!(initial.digest, revised.digest);
    let mut resolved = review(&revised);
    resolved.rationale = "Fixture review now accounts for the additional context.".into();
    resolved.supersedes = vec![unresolved.digest().unwrap()];
    evidence::record(&inventory, &revised, &resolved).unwrap();
    let report = evidence::check(&inventory).unwrap();
    assert!(report.is_ok(), "{}", report.render(&inventory));
    assert_eq!(
        fs::read(&old_path).unwrap(),
        old_bytes,
        "supersession must retain the original evidence"
    );

    let other = ReviewBundle::prepare(&inventory, "model.variable", &[]).unwrap();
    let other_review = review(&other);
    let mut wrong_unit = resolved;
    wrong_unit.supersedes = vec![other_review.digest().unwrap()];
    assert!(
        evidence::record(&inventory, &revised, &wrong_unit).is_err(),
        "a review cannot supersede another unit's evidence"
    );
}

#[test]
fn stale_supersession_cannot_fall_back_to_an_independent_positive_review() {
    let fixture = Fixture::new();
    // This positive review will remain current throughout the scenario.
    fixture.complete_reviews();
    let inventory = fixture.inventory();
    let initial = fixture.bundle();
    let mut mismatch = review(&initial);
    mismatch.conclusion = Conclusion::Mismatch;
    mismatch.rationale = "The fixture reviewer reports a mismatch.".into();
    evidence::record(&inventory, &initial, &mismatch).unwrap();

    fixture.write(
        "resolution.txt",
        "Extra context justifies the revised fixture conclusion.\n",
    );
    let revised =
        ReviewBundle::prepare(&inventory, "model.empty", &["resolution.txt".into()]).unwrap();
    let mut resolved = review(&revised);
    resolved.supersedes = vec![mismatch.digest().unwrap()];
    evidence::record(&inventory, &revised, &resolved).unwrap();
    assert!(evidence::check(&inventory).unwrap().is_ok());

    fixture.write(
        "resolution.txt",
        "The justification changed and needs a new review.\n",
    );
    let report = evidence::check(&fixture.inventory()).unwrap();
    assert!(!report.is_ok(), "a stale superseding review hid the mismatch while the checker fell back to another positive review");
    let diagnostic = report.render(&fixture.inventory());
    assert!(diagnostic.contains("stale"), "{diagnostic}");
    assert!(diagnostic.contains("resolution.txt"), "{diagnostic}");
}

#[test]
fn explicit_dependencies_and_unit_links_must_resolve() {
    let fixture = Fixture::new();
    for source in [
        MODEL.replace(":uses: model.variable", ":uses: model.missing"),
        MODEL.replace(
            "The empty list",
            "See {anchor-ref}`model.missing`. The empty list",
        ),
        MODEL.replace(
            "The empty list",
            "See [the missing unit](#claim-model.missing). The empty list",
        ),
    ] {
        fixture.write("md/model.md", &source);
        let error = Inventory::load(&fixture.0)
            .err()
            .expect("unresolved unit reference must fail");
        assert!(format!("{error:#}").contains("model.missing"));
    }

    // Referencing a real unit supplies its exact inputs even without :uses:.
    fixture.write(
        "md/model.md",
        &MODEL.replace(":uses: model.variable\n", "").replace(
            "The empty list",
            "See {anchor-ref}`model.variable`. The empty list",
        ),
    );
    let bundle = fixture.bundle();
    assert!(bundle
        .inputs
        .iter()
        .any(|input| input.key == "unit:model.variable"));
    assert!(bundle
        .inputs
        .iter()
        .any(|input| input.key == "lean:Fixture:Variable"));
}

#[test]
fn removed_obligations_cannot_evade_evidence_validation() {
    for chapter in ["md/model.md", "md/non-strict.md"] {
        for source in [
            "```{obligation} model.pending\n\nShow that allocation preserves well-formedness.\n```\n",
            "```{obligation}pending\nvars = variables()\nvars.x = uninitialized()\n```\n",
            "```{obligation} model.pending\n:lean: Fixture:missing\n\nShow that allocation preserves well-formedness.\n```\n",
            "{obligation}`model.pending` Show that allocation preserves well-formedness.\n",
            "> ```{obligation} model.pending\n> Unfinished claim.\n> ```\n",
            "- ```{obligation} model.pending\n  Unfinished claim.\n  ```\n",
            "> {obligation}`model.pending` Unfinished claim.\n",
            "- {obligation}`model.pending` Unfinished claim.\n",
            "```{definition} Fixture:empty\n{obligation}`model.pending` Unfinished claim.\n```\n",
            "````{definition} Fixture:empty\n```{obligation} model.pending\nUnfinished claim.\n```\n````\n",
            "```{definition} model.draft\n:status: draft\n\n{obligation}`model.pending` Unfinished claim.\n```\n",
        ] {
            let fixture = Fixture::new();
            // The fixture already has current reviews, so introducing an
            // unsupported claim outside strict coverage must not leave those
            // reviews sufficient to pass the checker.
            fixture.complete_reviews();
            let contents = if chapter == "md/model.md" {
                format!("{MODEL}\n{source}")
            } else {
                source.to_owned()
            };
            fixture.write(chapter, &contents);
            let error = Inventory::load(&fixture.0)
                .err()
                .expect("removed obligation syntax must fail the inventory");
            let diagnostic = format!("{error:#}");
            assert!(diagnostic.contains("obligation"), "{diagnostic}");
            assert!(diagnostic.contains("removed"), "{diagnostic}");
            assert!(diagnostic.contains(chapter), "{diagnostic}");
        }
    }
}

#[test]
fn draft_definitions_can_be_prepared_but_require_formalization_before_review() {
    let fixture = Fixture::new();
    let source = "# Draft model\n\n```{definition} model.draft\n:status: draft\n\nEvaluation returns a reference and updated storage.\n```\n";
    fixture.write("md/model.md", source);
    let inventory = fixture.inventory();
    let unit = inventory.unit("model.draft").unwrap();
    assert!(unit.draft);
    assert_eq!(unit.kind, mdbook_dada::units::UnitKind::Definition);
    assert!(inventory.required.contains("model.draft"));

    let bundle = ReviewBundle::prepare(&inventory, "model.draft", &[]).unwrap();
    assert!(bundle
        .inputs
        .iter()
        .any(|input| input.key == "unit:model.draft"));
    evidence::save_bundle(&inventory, &bundle).unwrap();
    let error = evidence::record(&inventory, &bundle, &review(&bundle)).unwrap_err();
    let message = format!("{error:#}");
    assert!(message.contains("draft unit model.draft"), "{message}");
    assert!(message.contains("formalization"), "{message}");

    let report = evidence::check(&inventory).unwrap();
    assert!(!report.is_ok());
    assert_eq!(report.statuses.len(), 1);
    assert_eq!(report.statuses[0].evidence, "draft");
    assert_eq!(report.statuses[0].correspondence, "not asserted");
    assert_eq!(report.statuses[0].mechanical, "not recorded");
    let diagnostic = report.render(&inventory);
    assert!(diagnostic.contains("md/model.md:"), "{diagnostic}");
    assert!(
        diagnostic.contains("requires formalization"),
        "{diagnostic}"
    );
    assert!(
        diagnostic.contains("remove `:status: draft`"),
        "{diagnostic}"
    );

    fixture.write("md/model.md", &source.replace(":status: draft\n", ""));
    assert!(
        Inventory::load(&fixture.0).is_err(),
        "removing draft status must restore the definition's citation requirement"
    );
}

#[test]
fn draft_status_cannot_hide_missing_or_wrong_kind_citations() {
    let fixture = Fixture::new();
    fixture.write("lean/Fixture.lean", "theorem proved : True := by trivial\n");
    for target in ["Fixture:missing", "malformed-target", "Fixture:proved"] {
        fixture.write(
            "md/model.md",
            &format!("# Draft model\n\n```{{definition}} model.draft\n:status: draft\n:lean: {target}\n\nEvaluation returns a reference and updated storage.\n```\n"),
        );
        let inventory = fixture.inventory();
        assert!(ReviewBundle::prepare(&inventory, "model.draft", &[]).is_err());
        let report = evidence::check(&inventory).unwrap();
        assert!(!report.is_ok());
        assert_eq!(report.statuses[0].evidence, "invalid sources");
        let diagnostic = report.render(&inventory);
        assert!(diagnostic.contains(target), "{diagnostic}");
    }
}

#[test]
fn changing_an_approved_unit_to_draft_cannot_reuse_or_forge_approval() {
    let fixture = Fixture::new();
    fixture.complete_reviews();
    assert!(evidence::check(&fixture.inventory()).unwrap().is_ok());
    fixture.write(
        "md/model.md",
        &MODEL.replace(
            "```{definition} model.variable\n",
            "```{definition} model.variable\n:status: draft\n",
        ),
    );
    let inventory = fixture.inventory();
    let bundle = ReviewBundle::prepare(&inventory, "model.variable", &[]).unwrap();
    let positive = review(&bundle);
    assert!(evidence::record(&inventory, &bundle, &positive).is_err());

    // A fabricated current record is no more authoritative than the old one.
    // This fixture attack must not let draft status pass the evidence gate.
    evidence::save_bundle(&inventory, &bundle).unwrap();
    fixture.write(
        &format!(
            "evidence/records/model.variable/{}.json",
            positive.digest().unwrap()
        ),
        &serde_json::to_string(&positive).unwrap(),
    );
    let report = evidence::check(&inventory).unwrap();
    assert!(!report.is_ok());
    let status = report
        .statuses
        .iter()
        .find(|status| status.unit == "model.variable")
        .unwrap();
    assert_eq!(status.evidence, "draft");
    assert_eq!(status.correspondence, "not asserted");
    assert!(report
        .issues
        .iter()
        .any(|issue| issue.unit.as_deref() == Some("model.variable")));
}

#[test]
fn reviewed_unit_depending_on_a_draft_cannot_complete_the_required_inventory() {
    let fixture = Fixture::new();
    fixture.write(
        "md/model.md",
        &MODEL.replace(":lean: Fixture:Variable", ":status: draft"),
    );
    let inventory = fixture.inventory();
    let bundle = fixture.bundle();
    assert!(bundle.inputs.iter().any(
        |input| input.key == "unit:model.variable" && input.content.contains(":status: draft")
    ));
    evidence::record(&inventory, &bundle, &review(&bundle)).unwrap();
    let report = evidence::check(&inventory).unwrap();
    assert!(!report.is_ok());
    let status = report
        .statuses
        .iter()
        .find(|status| status.unit == "model.empty")
        .unwrap();
    assert_eq!(status.correspondence, "corresponds");
    assert!(report
        .issues
        .iter()
        .any(|issue| issue.unit.as_deref() == Some("model.variable")));
}

#[cfg(unix)]
#[test]
fn generated_inputs_cannot_be_reintroduced_through_symlink_aliases() {
    let fixture = Fixture::new();
    let inventory = fixture.inventory();
    for directory in ["evidence", "target", "book"] {
        fixture.write(
            &format!("{directory}/generated.txt"),
            "Generated output is not source evidence.\n",
        );
        let alias = format!("{directory}-alias.txt");
        std::os::unix::fs::symlink(
            fixture.0.join(directory).join("generated.txt"),
            fixture.0.join(&alias),
        )
        .unwrap();
        assert!(
            ReviewBundle::prepare(&inventory, "model.empty", &[alias]).is_err(),
            "generated {directory} input was accepted through a symlink"
        );
    }
}

#[test]
fn authored_includes_and_nested_citations_cannot_acquire_evidence() {
    let fixture = Fixture::new();
    for body in [
        "{{#include details.txt}}",
        "{{#rustdoc_include example.rs}}",
        "{{#playground example.rs}}",
        "```{grammar} Fixture:Variable\nx ::= Nat\n```",
    ] {
        fixture.write("md/model.md", &format!("````{{definition}} model.value\n:rust: mdbook-dada/src/lib.rs:validate\n\n{body}\n````\n"));
        assert!(Inventory::load(&fixture.0).is_err(), "{body}");
    }
}

fn configured_context(fixture: &Fixture, lean_root: &str) -> serde_json::Value {
    serde_json::json!({"root": fixture.0, "config": {"book": {"src": "md"}, "preprocessor": {"dada": {"lean-source": lean_root}}}})
}

fn chapter(source: &str) -> serde_json::Value {
    serde_json::json!({"items": [{"Chapter": {"path": "model.md", "source_path": "model.md", "content": source, "sub_items": []}}]})
}

#[test]
fn configured_lean_root_is_shared_by_rendering_and_evidence() {
    let fixture = Fixture::new();
    fixture.complete_reviews();
    let original = fixture.bundle();
    assert!(original
        .inputs
        .iter()
        .any(|input| input.key == "tool:book.toml"));
    for file in [
        "Fixture.lean",
        "lean-toolchain",
        "lakefile.toml",
        "lake-manifest.json",
    ] {
        fixture.write(
            &format!("formal/model/{file}"),
            &fs::read_to_string(fixture.0.join("lean").join(file)).unwrap(),
        );
    }
    fixture.write(
        "formal/model/Fixture.lean",
        "abbrev Variable := Nat\ndef empty : List Variable := [2]\n",
    );
    fixture.write(
        "book.toml",
        "[book]\nsrc = \"md\"\n[preprocessor.dada]\nlean-source = \"formal/model\"\n",
    );
    let inventory = fixture.inventory();
    assert!(!evidence::check(&inventory).unwrap().is_ok());
    let bundle = fixture.bundle();
    let selected = bundle
        .inputs
        .iter()
        .find(|input| input.key == "lean:Fixture:empty")
        .unwrap();
    assert_eq!(selected.path, "formal/model/Fixture.lean");
    assert!(selected.content.contains(":= [2]"));
    assert!(bundle
        .inputs
        .iter()
        .any(|input| input.key == "context:formal/model/Fixture.lean"));
    assert!(!bundle
        .inputs
        .iter()
        .any(|input| input.path.starts_with("lean/")));
    let mut book = chapter(MODEL);
    mdbook_dada::process_configured(&configured_context(&fixture, "formal/model"), &mut book)
        .unwrap();
    assert!(book.to_string().contains(":= [2]"));
    let mut book = chapter(MODEL);
    assert!(
        mdbook_dada::process_configured(&configured_context(&fixture, "lean"), &mut book).is_err()
    );
    // Rust selections use the project root, not the parent of the Lean directory.
    let rust =
        "```{definition} meta.check\n:rust: mdbook-dada/src/lib.rs:validate\n\nValidation.\n```";
    fixture.write("md/model.md", rust);
    let mut book = chapter(rust);
    mdbook_dada::process_configured(&configured_context(&fixture, "formal/model"), &mut book)
        .unwrap();
    assert!(book.to_string().contains("pub fn validate"));
}

#[test]
fn preexpanded_includes_cannot_bypass_original_source_validation() {
    let fixture = Fixture::new();
    let raw =
        "```{definition} model.variable\n:lean: Fixture:Variable\n\n{{#include details.txt}}\n```";
    fixture.write("md/model.md", raw);
    let expanded = raw.replace("{{#include details.txt}}", "The value is two.");
    let mut book = chapter(&expanded);
    let error = mdbook_dada::process_configured(&configured_context(&fixture, "lean"), &mut book)
        .unwrap_err();
    assert!(format!("{error:#}").contains("directives are unsupported"));
    // An include outside a unit cannot introduce a new unit unknown to the inventory.
    fixture.write("md/model.md", "{{#include units.txt}}\n");
    let mut book = chapter(MODEL);
    let error = mdbook_dada::process_configured(&configured_context(&fixture, "lean"), &mut book)
        .unwrap_err();
    assert!(format!("{error:#}").contains("preprocessing changed structured units"));
    // Other preprocessors also cannot rewrite claims while leaving evidence current.
    fixture.write("md/model.md", MODEL);
    let mut book = chapter(&MODEL.replace("natural number", "Boolean"));
    assert!(
        mdbook_dada::process_configured(&configured_context(&fixture, "lean"), &mut book).is_err()
    );
}

#[test]
#[ignore = "requires the mdbook executable; run with --ignored after installing book tools"]
fn actual_mdbook_pipeline_rejects_includes_in_reviewed_content() {
    let fixture = Fixture::new();
    fixture.write("md/SUMMARY.md", "# Summary\n\n- [Model](model.md)\n");
    fixture.write("md/details.txt", "The value is one.\n");
    fixture.write("md/model.md", "```{definition} model.variable\n:lean: Fixture:Variable\n\n{{#include details.txt}}\n```\n");
    let command =
        serde_json::to_string(&format!("\"{}\"", env!("CARGO_BIN_EXE_mdbook-dada"))).unwrap();
    fixture.write("book.toml", &format!("[book]\nsrc = \"md\"\n[preprocessor.dada]\ncommand = {command}\nafter = [\"links\"]\nlean-source = \"lean\"\n"));
    for contents in ["The value is one.", "The value is two."] {
        fixture.write("md/details.txt", contents);
        let output = std::process::Command::new("mdbook")
            .arg("build")
            .arg(&fixture.0)
            .output()
            .expect("install mdbook before running this test");
        assert!(!output.status.success());
        let error = String::from_utf8_lossy(&output.stderr);
        assert!(
            error.contains("directives are unsupported inside structured units"),
            "{error}"
        );
    }
}

use mdbook_dada::{
    lean,
    units::{self, UnitKind},
};
use serde_json::json;
use std::{
    path::{Path, PathBuf},
    sync::atomic::{AtomicUsize, Ordering},
};

struct Sources(PathBuf);
impl Sources {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let root = std::env::temp_dir().join(format!(
            "dada-units-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(root.join("lean")).unwrap();
        std::fs::write(root.join("lean/Model.lean"), "inductive Thing where\n  | empty\ndef initial : Thing := .empty\ntheorem initial_is_empty : initial = Thing.empty := by\n  rfl\ninductive Step : Thing → Thing → Prop where\n  | same (t : Thing) : Step t t\n-- ANCHOR: basic\nexample : initial = Thing.empty := by\n  rfl\n-- ANCHOR_END: basic\n").unwrap();
        std::fs::write(
            root.join("tool.rs"),
            "pub fn check() -> bool { true }\n#[test]\nfn checks() { assert!(check()); }\n",
        )
        .unwrap();
        Self(root)
    }
    fn lean(&self) -> PathBuf {
        self.0.join("lean")
    }
}
impl Drop for Sources {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

fn render(source: &str, root: &Path) -> anyhow::Result<String> {
    let mut book =
        json!({"items":[{"Chapter":{"path":"model.md","content":source,"sub_items":[]}}]});
    mdbook_dada::process_with_lean(&mut book, Some(root))?;
    Ok(book["items"][0]["Chapter"]["content"]
        .as_str()
        .unwrap()
        .to_owned())
}

#[test]
fn exact_authored_units_preserve_unicode_latex_and_crlf() {
    let raw = "```{definition} model.initial\r\n:lean: Model:initial\r\n:uses: model.thing\r\n\r\nThe initial α is empty.\r\n\r\n\\\\[ α = \\mathsf{empty} \\\\]\r\n```\r\n";
    let source = format!("# α model\r\n\r\n{raw}");
    let units = units::parse(&source, "md/model.md").unwrap();
    assert_eq!(units.len(), 1);
    let unit = &units[0];
    assert_eq!(unit.id, "model.initial");
    assert_eq!(unit.kind, UnitKind::Definition);
    assert_eq!(unit.source_path, "md/model.md");
    assert_eq!(unit.raw, source[unit.range.clone()]);
    assert_eq!(unit.raw.trim_end(), raw.trim_end());
    assert_eq!(unit.lean, ["Model:initial"]);
    assert_eq!(unit.uses, ["model.thing"]);
    assert!(unit.body.contains("α = \\mathsf{empty}"));
    assert!(!unit.body.contains(":lean:"));
    units::validate_coverage(&source, "md/model.md").unwrap();
}

#[test]
fn legacy_blocks_and_literal_authoring_examples_are_not_units() {
    let source = "```{definition} Model:Thing\nOld prose.\n```\n\n````markdown\n```{definition} literal.id\n:lean: Missing:Thing\n\nLiteral.\n```\n````\n\n    ```{definition} also.literal\n";
    assert!(units::parse(source, "model.md").unwrap().is_empty());
}

#[test]
fn malformed_units_fail_with_source_location() {
    for source in [
        "```{definition} two ids\n:lean: Model:Thing\n\nText.\n```",
        "```{definition} no.source\nText.\n```",
        "```{definition} bad.option\n:unknown: Thing\n\nText.\n```",
        "```{definition} repeated.option\n:lean: Model:Thing\n:lean: Model:Thing\n\nText.\n```",
        "```{definition} repeated.target\n:lean: Model:Thing Model:Thing\n\nText.\n```",
        "```{definition} mixed.sources\n:lean: Model:Thing\n:rust: tool.rs:check\n\nText.\n```",
        "```{definition} delayed.option\n\n:lean: Model:Thing\nText.\n```",
        "```{definition} delayed.uses\n:lean: Model:Thing\n\n:uses: other.id\nText.\n```",
        "```{definition} no.end\n:lean: Model:Thing\n\nText.",
        "```{definition} empty.body\n:lean: Model:Thing\n\n```",
        "```{theorem} many.theorems\n:lean: Model:first Model:second\n\nText.\n```",
        "```{definition} self.cycle\n:lean: Model:Thing\n:uses: self.cycle\n\nText.\n```",
        "```{definition} tests.only\n:tests: tool.rs:checks\n\nText.\n```",
    ] {
        let error = format!("{:#}", units::parse(source, "md/model.md").unwrap_err());
        assert!(error.contains("md/model.md:1"), "{error}");
    }
}

#[test]
fn duplicate_and_nested_units_fail() {
    let unit = "```{definition} pending\n:status: draft\n\nExplain the proposed definition.\n```\n";
    assert!(units::parse(&format!("{unit}\n{unit}"), "model.md").is_err());
    assert!(units::parse(
        &format!("````{{definition}} outer\n:status: draft\n\n{unit}\n````"),
        "model.md"
    )
    .is_err());
}

#[test]
fn coverage_rejects_unattached_prose_and_legacy_blocks() {
    for source in [
        "# Title\n\nLoose prose.",
        "# Title\n\n```{definition} Model:Thing\nText.\n```",
        "# Title\n\n<!-- concealed prose -->",
    ] {
        assert!(units::validate_coverage(source, "md/model.md").is_err());
    }
    units::validate_coverage(
        "# Title\n\n```{definition} pending\n:status: draft\n\nA proposed definition.\n```",
        "model.md",
    )
    .unwrap();
}

#[test]
fn links_form_dependencies_but_literals_do_not() {
    let body = "See {anchor-ref}`a` and [B](other.md#claim-b), [C](#c), [B again](#claim-b).\n\n`{anchor-ref}`literal\n\n```text\n{anchor-ref}`hidden`\n[H](#hidden)\n```\n\n[Remote](https://example.com/#remote)";
    assert_eq!(units::linked_ids(body).unwrap(), ["a", "b", "c"]);
    assert_eq!(units::required_linked_ids(body).unwrap(), ["a", "b"]);
    assert!(units::linked_ids(r"\\({anchor-ref}`math.literal`\\)")
        .unwrap()
        .is_empty());
}

#[test]
fn structured_units_render_identified_headers_and_exact_lean_views() {
    let files = Sources::new();
    for (kind, citation, body, expected) in [
        (
            "definition",
            "Model:initial",
            "The initial object is empty.",
            "def initial",
        ),
        (
            "grammar",
            "Model:Thing",
            "t ::= \\mathsf{empty}",
            "inductive Thing",
        ),
        ("judgment", "Model:Step", "t \\to t'", "inductive Step"),
        ("rule", "Model:Step.same", "\\frac{}{t \\to t}", "| same"),
        (
            "theorem",
            "Model:initial_is_empty",
            "The initial object is empty.",
            "theorem initial_is_empty",
        ),
        (
            "lemma",
            "Model:initial_is_empty",
            "The initial object is empty.",
            "theorem initial_is_empty",
        ),
        (
            "example",
            "Model:basic",
            "The initial object is empty.",
            "example : initial",
        ),
    ] {
        let source = format!("```{{{kind}}} model.unit\n:lean: {citation}\n\n{body}\n```\n\nSee {{anchor-ref}}`model.unit`.");
        let output = render(&source, &files.lean()).unwrap();
        assert_eq!(output.matches("id=\"claim-model.unit\"").count(), 1);
        assert!(output.contains("href=\"#claim-model.unit\""));
        assert!(output.contains("class=\"view-options\""));
        assert!(output.contains("value=\"lean\""));
        assert!(!output.contains(":lean:"));
        let selected = lean::select(
            &files.lean(),
            citation,
            UnitKind::parse(&format!("{{{kind}}}")).unwrap(),
        )
        .unwrap();
        assert!(
            selected.selected.contains(expected),
            "{}",
            selected.selected
        );
        assert!(selected.source.contains("theorem initial_is_empty"));
        assert!(selected.path.is_absolute());
    }
}

#[test]
fn new_units_retain_kind_checks() {
    let files = Sources::new();
    assert!(render(
        "```{theorem} wrong.kind\n:lean: Model:initial\n\nClaim.\n```",
        &files.lean()
    )
    .is_err());
    assert!(render(
        "```{theorem} rust.is.not.proof\n:rust: tool.rs:check\n\nClaim.\n```",
        &files.lean()
    )
    .is_err());
    assert!(render(
        "```{definition} wrong.kind\n:lean: Model:initial_is_empty\n\nClaim.\n```",
        &files.lean()
    )
    .is_err());
}

#[test]
fn removed_obligation_syntax_is_rejected_at_every_authoring_entry_point() {
    let files = Sources::new();
    assert!(UnitKind::parse("{obligation}").is_none());
    assert!(serde_json::from_str::<UnitKind>("\"obligation\"").is_err());
    for source in [
        "```{obligation} model.pending\nUnfinished.\n```",
        "```{obligation} Model:initial\nUnfinished.\n```",
        "```{obligation}pending\nvars = variables()\nvars.x = uninitialized()\n```",
        "{obligation}`pending` Unfinished.",
        "> ```{obligation} pending\n> Unfinished.\n> ```",
        "- ```{obligation} pending\n  Unfinished.\n  ```",
        "```{definition} Model:initial\n{obligation}`pending` Unfinished.\n```",
        "````{definition} model.draft\n:status: draft\n\n```{obligation} pending\nUnfinished.\n```\n````",
    ] {
        let error = format!("{:#}", units::parse(source, "model.md").unwrap_err());
        assert!(error.contains("model.md"), "{error}");
        assert!(error.contains("{obligation} has been removed"), "{error}");
        assert!(error.contains(":status: draft"), "{error}");
        assert!(render(source, &files.lean()).is_err(), "{source}");
    }
}

#[test]
fn removed_syntax_remains_literal_in_code_samples_and_escaped_roles() {
    let files = Sources::new();
    for source in [
        "````text\n```{obligation} pending\nUnfinished.\n```\n````",
        "```text\n{obligation}`pending`\n```",
        "`{obligation}`pending",
        "{obligation}``pending``",
        "\\{obligation}`pending`",
    ] {
        assert!(units::parse(source, "model.md").unwrap().is_empty());
        assert_eq!(render(source, &files.lean()).unwrap(), source);
    }
}

#[test]
fn drafts_keep_their_semantic_kind_without_claiming_a_formalization() {
    let files = Sources::new();
    for kind in [
        "definition",
        "grammar",
        "judgment",
        "rule",
        "theorem",
        "lemma",
        "example",
    ] {
        let source = format!("```{{{kind}}} model.draft\n:status: draft\n\nProposed content.\n```");
        let parsed = units::parse(&source, "model.md").unwrap();
        assert!(parsed[0].draft);
        assert_eq!(
            parsed[0].kind,
            UnitKind::parse(&format!("{{{kind}}}")).unwrap()
        );
        let output = render(&source, &files.lean()).unwrap();
        assert!(output.contains(&format!("{kind}: model.draft")));
        assert!(output.contains("class=\"block-label unit-status\""));
        assert!(output.contains(">Draft</span>"));
        assert!(!output.contains("proof obligation"));
        assert!(!output.contains("type=\"radio\""));
        assert!(!output.contains(":status:"));
        assert!(units::parse(&source.replace(":status: draft\n", ""), "model.md").is_err());
    }

    let current = render(
        "```{definition} model.current\n:lean: Model:initial\n\nCurrent definition.\n```",
        &files.lean(),
    )
    .unwrap();
    assert!(!current.contains("unit-status"));
    assert!(current.contains("value=\"lean\""));
}

#[test]
fn draft_status_is_explicit_and_does_not_relax_citation_checks() {
    let files = Sources::new();
    for options in [
        ":status:",
        ":status: checked",
        ":status: draft checked",
        ":status: draft\n:status: draft",
    ] {
        let source = format!("```{{definition}} invalid.status\n{options}\n\nText.\n```");
        let error = format!("{:#}", units::parse(&source, "model.md").unwrap_err());
        assert!(error.contains("model.md:1"), "{error}");
    }
    for (kind, citation) in [
        ("definition", ":lean: Model:missing"),
        ("definition", ":lean: Model:initial_is_empty"),
        ("theorem", ":lean: Model:initial"),
        ("theorem", ":rust: tool.rs:check"),
        ("example", ":lean: Model:initial_is_empty"),
    ] {
        let source =
            format!("```{{{kind}}} invalid.citation\n:status: draft\n{citation}\n\nText.\n```");
        assert!(render(&source, &files.lean()).is_err(), "{source}");
    }
    let output = render(
        "```{definition} model.draft\n:status: draft\n:lean: Model:initial\n\nProposed explanation.\n```",
        &files.lean(),
    )
    .unwrap();
    assert!(output.contains("value=\"lean\""));
    assert!(output.contains(">Draft</span>"));
}

#[test]
fn meta_units_show_named_rust_implementation_and_test() {
    let files = Sources::new();
    let output = render("```{definition} meta.check\n:rust: tool.rs:check\n:tests: tool.rs:checks\n\nThe checker accepts this input.\n```", &files.lean()).unwrap();
    assert!(output.contains("value=\"rust\""));
    assert!(output.contains("pub fn check()"));
    assert!(output.contains("fn checks()"));
    assert!(!output.contains(":rust:"));
}

#[test]
fn structured_units_reject_includes_and_nested_legacy_citations() {
    let files = Sources::new();
    for body in [
        "{{#include details.txt}}",
        "{{ #rustdoc_include example.rs }}",
        "```rust\n{{#playground example.rs}}\n```",
        "```{grammar} Model:Thing\nt ::= empty\n```",
        "```{judgment} Model:Step\nt \\to t\n```",
        "```{rule} Model:Step.same\nt \\to t\n```",
    ] {
        for citation in [":lean: Model:initial", ":rust: tool.rs:check"] {
            let source = format!("````{{definition}} model.unit\n{citation}\n\n{body}\n````");
            assert!(units::parse(&source, "md/model.md").is_err(), "{source}");
            assert!(render(&source, &files.lean()).is_err(), "{source}");
        }
    }
    // Existing citation-first authoring outside reviewed units remains supported.
    render(
        "````{definition} Model:initial\nText.\n\n```{grammar} Model:Thing\nt ::= empty\n```\n````",
        &files.lean(),
    )
    .unwrap();
}

#[test]
fn rule_citations_cannot_select_an_indented_siblings_constructor() {
    let files = Sources::new();
    std::fs::write(files.lean().join("Sibling.lean"), "inductive First where\n  | first\n  inductive Second where\n  | second\n#check Second.second\n").unwrap();
    for kind in [UnitKind::Grammar, UnitKind::Judgment, UnitKind::Definition] {
        let error = lean::select(&files.lean(), "Sibling:First", kind).unwrap_err();
        assert!(format!("{error:#}").contains("no other commands"));
    }
    let error = lean::select(&files.lean(), "Sibling:First.second", UnitKind::Rule).unwrap_err();
    assert!(format!("{error:#}").contains("no other commands"));
    assert!(render(
        "```{rule} model.invalid\n:lean: Sibling:First.second\n\nP\n```",
        &files.lean()
    )
    .is_err());
    assert!(render("```{rule} Sibling:First.second\nP\n```", &files.lean()).is_err());
}

#[test]
fn rule_selections_preserve_final_literal_tokens() {
    let files = Sources::new();
    for (ty, term) in [
        ("String", r#""zero""#),
        ("String", "r#\"raw -- /- «text»\"#"),
        ("Char", "'α'"),
        ("Char", "'\\n'"),
        ("Nat", "«some index»"),
    ] {
        let header = format!("inductive Indexed : {ty} → Type where");
        let case = format!("  | zero : Indexed {term}");
        for ending in [
            "\n",
            " -- attached\n",
            "\n  -- next constructor\n  | next : Indexed default\n",
        ] {
            std::fs::write(
                files.lean().join("Indexed.lean"),
                format!("{header}\n{case}{ending}"),
            )
            .unwrap();
            let selected =
                lean::select(&files.lean(), "Indexed:Indexed.zero", UnitKind::Rule).unwrap();
            assert!(
                selected.selected.starts_with(&format!("{header}\n{case}")),
                "{}",
                selected.selected
            );
            assert_eq!(
                selected.selected.contains("-- attached"),
                ending.contains("-- attached")
            );
            assert!(!selected.selected.contains("next constructor"));
            assert!(!selected.selected.contains("| next"));
            let output = render(
                "```{rule} model.literal\n:lean: Indexed:Indexed.zero\n\nP\n```",
                &files.lean(),
            )
            .unwrap();
            assert!(output.contains(&mdbook_dada::escape(term)), "{output}");
        }
    }
}

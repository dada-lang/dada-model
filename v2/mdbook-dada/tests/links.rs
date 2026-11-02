use mdbook_dada::{
    inventory::Inventory,
    links::{Direction, LinkInventory, LinkSyntax, LinkTarget, Links, TargetKind},
};
use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicUsize, Ordering},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new(summary: &str, chapters: &[(&str, String)]) -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let root = std::env::temp_dir().join(format!(
            "dada-links-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(root.join("md")).unwrap();
        fs::create_dir_all(root.join("lean")).unwrap();
        fs::write(
            root.join("book.toml"),
            "[book]\nsrc = 'md'\n[preprocessor.dada]\nlean-source = 'lean'\n",
        )
        .unwrap();
        fs::write(
            root.join("spec.json"),
            r#"{"schema":1,"chapters":["md/scope.md"],"policies":["policy.txt"]}"#,
        )
        .unwrap();
        fs::write(root.join("policy.txt"), "Review links.").unwrap();
        fs::write(root.join("md/scope.md"), unit("scope", "Scope.")).unwrap();
        fs::write(root.join("md/SUMMARY.md"), summary).unwrap();
        for (name, content) in chapters {
            let path = root.join("md").join(name);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, content).unwrap();
        }
        Self(root)
    }
    fn inventory(&self) -> Inventory {
        Inventory::load(&self.0).unwrap()
    }
    fn build(&self) -> anyhow::Result<LinkInventory> {
        Links::build(&Inventory::load(&self.0)?)
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn unit(id: &str, body: &str) -> String {
    format!("````{{definition}} {id}\n:status: draft\n\n{body}\n````\n")
}

#[test]
fn inventory_reads_markdown_reference_roles_and_math_with_exact_ranges() {
    let body = r"A [direct link](second.html#claim-second), [reference][ref], and {anchor-ref}`second`.

\\[ \href{second.html#claim-second}{\operatorname{target}_{x}} \\]

[ref]: second.md#claim-second

`[literal](missing.md)` and `\href{missing.md}{literal}`.

```text
[literal](missing.md)
\\[ \href{missing.md}{literal} \\]
```

<!-- [comment](missing.md) \\(\href{missing.md}{comment}\\) -->";
    let first = unit("first", body);
    let fixture = Fixture::new(
        "[First](first.md)\n- [Second](second.md)\n",
        &[
            ("first.md", first.clone()),
            ("second.md", unit("second", "Definition.")),
        ],
    );
    let inventory = fixture.inventory();
    let links = Links::build(&inventory).unwrap();
    let occurrences = &links.sources["first"].occurrences;
    assert_eq!(occurrences.len(), 4);
    assert_eq!(
        occurrences
            .iter()
            .map(|link| link.syntax)
            .collect::<Vec<_>>(),
        [
            LinkSyntax::Markdown,
            LinkSyntax::Markdown,
            LinkSyntax::AnchorRef,
            LinkSyntax::MathJax
        ]
    );
    for link in occurrences {
        assert_eq!(link.direction, Direction::Forward);
        assert!(first[link.source.range.clone()].contains(
            if link.syntax == LinkSyntax::Markdown {
                "["
            } else if link.syntax == LinkSyntax::MathJax {
                "\\href"
            } else {
                "{anchor-ref}"
            }
        ));
        assert!(
            matches!(&link.target, LinkTarget::Internal { target } if target.key == "md/second.md#claim-second")
        );
        assert!(links.occurrence(&link.id).is_some());
    }
    assert_eq!(links.inputs(&inventory).len(), inventory.sources.len());
}

#[test]
fn reference_definitions_outside_unit_and_bare_math_directives_are_inventoried() {
    let first = format!(
        "{}\n[outside]: second.md#claim-second\n",
        unit("first", "See [the definition][outside].")
    );
    let math = "```{grammar} grammar\n:status: draft\n\np ::= \\href{second.html#claim-second}{x}\\mid p.f\n```\n".to_owned();
    let fixture = Fixture::new(
        "- [First](first.md)\n- [Math](math.md)\n- [Second](second.md)",
        &[
            ("first.md", first),
            ("math.md", math),
            ("second.md", unit("second", "Definition.")),
        ],
    );
    let links = fixture.build().unwrap();
    assert_eq!(links.sources["first"].occurrences.len(), 1);
    assert_eq!(links.sources["grammar"].occurrences.len(), 1);
    assert_eq!(
        links.sources["grammar"].occurrences[0].syntax,
        LinkSyntax::MathJax
    );
}

#[test]
fn order_comes_from_summary_and_byte_position_not_filename_or_unit_id() {
    let fixture = Fixture::new("[Last filename first](z.md)\n- [Group](group.md)\n  - [Then A](a.md)\n\n[Appendix](appendix.md)", &[
        ("z.md", unit("z", "[forward](a.md#claim-a)")),
        ("group.md", "# Group".into()),
        ("a.md", format!("{}{}", unit("a", "[back](z.md#claim-z), [later](#claim-local), [self](#claim-a)"), unit("local", "[earlier](#claim-a)"))),
        ("appendix.md", unit("appendix", "[earlier](a.md#claim-a)")),
        ("hidden.md", unit("hidden", "[unordered](a.md#claim-a)")),
    ]);
    let links = fixture.build().unwrap();
    assert_eq!(
        links
            .chapters
            .iter()
            .map(|c| c.path.as_str())
            .collect::<Vec<_>>(),
        ["md/z.md", "md/group.md", "md/a.md", "md/appendix.md"]
    );
    assert_eq!(
        links.sources["z"].occurrences[0].direction,
        Direction::Forward
    );
    assert_eq!(
        links.sources["a"]
            .occurrences
            .iter()
            .map(|l| l.direction)
            .collect::<Vec<_>>(),
        [Direction::Backward, Direction::Forward, Direction::Local]
    );
    assert_eq!(
        links.sources["hidden"].occurrences[0].direction,
        Direction::Unordered
    );
    assert!(links
        .cycles
        .iter()
        .any(|cycle| cycle == &["a", "local", "z"]));
}

#[test]
fn headings_have_mdbook_ids_duplicates_and_explicit_ids() {
    let fixture = Fixture::new(
        "- [A](a.md)",
        &[(
            "a.md",
            format!(
                "# Über `thing`!\n\n# Über `thing`!\n\n# Named {{#explicit}}\n\n{}",
                unit(
                    "a",
                    "[one](#über-thing), [two](#%C3%BCber-thing-1), [named](#explicit)"
                )
            ),
        )],
    );
    let links = fixture.build().unwrap();
    assert!(links.sources["a"].occurrences.iter().all(|link| matches!(&link.target, LinkTarget::Internal { target } if target.kind == TargetKind::Heading)));
    assert_eq!(
        links.sources["a"].occurrences[1].direction,
        Direction::Backward
    );
}

#[test]
fn relative_paths_preserve_target_chapter_and_wrong_path_does_not_match_global_id() {
    let fixture = Fixture::new(
        "- [A](nested/a.md)\n- [B](b.md)",
        &[
            ("nested/a.md", unit("a", "[B](.././b.html#claim-b)")),
            ("b.md", unit("b", "B.")),
        ],
    );
    assert!(
        matches!(&fixture.build().unwrap().sources["a"].occurrences[0].target, LinkTarget::Internal { target } if target.key == "md/b.md#claim-b")
    );
    fs::write(
        fixture.0.join("md/nested/a.md"),
        unit("a", "[B](a.md#claim-b)"),
    )
    .unwrap();
    let error = format!("{:#}", fixture.build().unwrap_err());
    assert!(error.contains("md/nested/a.md:4"), "{error}");
    assert!(error.contains("path and anchor"), "{error}");
}

#[test]
fn source_root_escapes_and_ambiguous_local_urls_are_rejected() {
    for destination in [
        "../../outside.md",
        "%2e%2e/outside.md",
        "/a.md",
        "a.md?preview=true",
        "a.md#missing",
        "javascript:alert(1)",
    ] {
        let fixture = Fixture::new(
            "- [A](a.md)",
            &[("a.md", unit("a", &format!("[link](<{destination}>)")))],
        );
        assert!(fixture.build().is_err(), "accepted {destination}");
    }
}

#[test]
fn same_unit_destinations_retain_exact_location_and_future_notes_are_audit_sources() {
    let body = "See [later heading](#later).\n\n## Later\n\nThe definition is here.";
    let fixture = Fixture::new(
        "- [A](a.md)",
        &[(
            "a.md",
            format!(
                "{}\n```{{future-note}} future\n\n[definition](#claim-a)\n```",
                unit("a", body)
            ),
        )],
    );
    let links = fixture.build().unwrap();
    let reference = &links.sources["a"].occurrences[0];
    assert_eq!(reference.direction, Direction::Local);
    assert!(
        matches!(&reference.target, LinkTarget::Internal { target } if target.location.range.start > reference.source.range.start)
    );
    assert!(links.sources["future"].audit_required);
    assert_eq!(
        links.sources["future"].unit_kind,
        mdbook_dada::units::UnitKind::FutureNote
    );
    assert_eq!(links.sources["future"].occurrences.len(), 1);
}

#[test]
fn escaped_and_commented_math_hrefs_are_not_links_but_nested_link_labels_are() {
    let fixture = Fixture::new(
        "- [A](a.md)\n- [B](b.md)",
        &[
            (
                "a.md",
                unit(
                    "a",
                    r"\\[
% \href{missing.md}{comment}
\\href{missing.md}{escaped}
\href{b.html#claim-b}{\href{b.html#claim-b}{nested}}
\\]",
                ),
            ),
            ("b.md", unit("b", "B.")),
        ],
    );
    assert_eq!(fixture.build().unwrap().sources["a"].occurrences.len(), 2);
}

#[test]
fn duplicate_summary_entries_and_raw_html_links_fail_explicitly() {
    let fixture = Fixture::new("- [A](a.md)\n- [Again](a.md)", &[("a.md", unit("a", "A."))]);
    assert!(format!("{:#}", fixture.build().unwrap_err()).contains("duplicate chapter"));
    let fixture = Fixture::new(
        "- [A](a.md)",
        &[(
            "a.md",
            unit("a", "<a href=\"https://example.com\">link</a>"),
        )],
    );
    assert!(format!("{:#}", fixture.build().unwrap_err()).contains("HTML links"));
}

#[test]
fn current_book_links_have_resolvable_targets() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap();
    let inventory = Inventory::load(root).unwrap();
    let links = Links::build(&inventory).unwrap();
    assert_eq!(links.sources.len(), inventory.units.len());
}

#[test]
fn malformed_explicit_links_fail_instead_of_disappearing_or_panicking() {
    for body in [
        "See [missing][undefined].",
        "See [missing][].",
        r"\\[ \href{b.html#claim-b}{unclosed \\]",
        r"\\[ \href{b.html#claim-b} \\]",
        r"\\[ \href{\computed}{label} \\]",
    ] {
        let fixture = Fixture::new(
            "- [A](a.md)\n- [B](b.md)",
            &[("a.md", unit("a", body)), ("b.md", unit("b", "B."))],
        );
        let error = format!("{:#}", fixture.build().unwrap_err());
        assert!(error.contains("md/a.md:"), "{error}");
    }
}

#[test]
fn legacy_anchors_resolve_without_being_mistaken_for_structured_units() {
    let fixture = Fixture::new(
        "- [A](a.md)\n- [Legacy](legacy.md)",
        &[
            (
                "a.md",
                unit(
                    "a",
                    "See {anchor-ref}`legacy` and [legacy](legacy.html#claim-legacy).",
                ),
            ),
            (
                "legacy.md",
                "# Legacy\n\n{anchor}`legacy` This is a standalone old definition.\n".into(),
            ),
        ],
    );
    let links = fixture.build().unwrap();
    assert_eq!(links.sources["a"].occurrences.len(), 2);
    assert!(links.sources["a"].occurrences.iter().all(|link| matches!(&link.target, LinkTarget::Internal { target } if target.kind == TargetKind::LegacyAnchor && target.unit_id.is_none())));
}

#[test]
fn changed_summary_and_link_positions_change_serialized_inventory() {
    let fixture = Fixture::new(
        "- [A](a.md)\n- [B](b.md)",
        &[
            ("a.md", unit("a", "[B](b.md#claim-b)")),
            ("b.md", unit("b", "B.")),
        ],
    );
    let before = fixture.build().unwrap();
    fs::write(fixture.0.join("md/SUMMARY.md"), "- [B](b.md)\n- [A](a.md)").unwrap();
    let after = fixture.build().unwrap();
    assert_ne!(
        serde_json::to_vec(&before).unwrap(),
        serde_json::to_vec(&after).unwrap()
    );
    assert_eq!(
        after.sources["a"].occurrences[0].direction,
        Direction::Backward
    );
    fs::write(
        fixture.0.join("md/a.md"),
        unit("a", "Earlier introduction. [B](b.md#claim-b)"),
    )
    .unwrap();
    let shifted = fixture.build().unwrap();
    assert_eq!(
        after.sources["a"].occurrences[0].id,
        shifted.sources["a"].occurrences[0].id
    );
    assert_ne!(
        after.sources["a"].occurrences[0].source.range,
        shifted.sources["a"].occurrences[0].source.range
    );
}

#[test]
fn heading_and_chapter_links_enclosing_the_use_require_local_order_review() {
    let chapter = format!(
        "# Topic\n\n{}\n{}\n# Next topic\n",
        unit(
            "use",
            "See [topic](#topic) and [chapter](a.md) for the definition."
        ),
        unit("definition", "The definition is introduced after the use.")
    );
    let fixture = Fixture::new("- [A](a.md)", &[("a.md", chapter.clone())]);
    let links = fixture.build().unwrap();
    let references = &links.sources["use"].occurrences;
    assert!(references
        .iter()
        .all(|link| link.direction == Direction::Local));
    let LinkTarget::Internal { target } = &references[0].target else {
        panic!("internal heading expected")
    };
    assert_eq!(&chapter[target.anchor_location.range.clone()], "# Topic\n");
    assert!(chapter[target.location.range.clone()].contains("introduced after the use"));
    assert!(!chapter[target.location.range.clone()].contains("Next topic"));
}

#[test]
fn legacy_target_scope_includes_definition_and_stops_at_next_anchor() {
    let legacy = "{anchor}`one` First definition.\n\nMore explanation.\n\n{anchor}`two` Second definition.\n";
    let fixture = Fixture::new(
        "- [A](a.md)\n- [Legacy](legacy.md)",
        &[
            ("a.md", unit("a", "[one](legacy.md#claim-one)")),
            ("legacy.md", legacy.into()),
        ],
    );
    let links = fixture.build().unwrap();
    let target = &links.targets["md/legacy.md#claim-one"];
    assert_eq!(
        &legacy[target.anchor_location.range.clone()],
        "{anchor}`one`"
    );
    assert!(legacy[target.location.range.clone()].contains("More explanation"));
    assert!(!legacy[target.location.range.clone()].contains("Second definition"));
}

#[test]
fn external_and_asset_links_remain_visible_for_classification() {
    let fixture = Fixture::new("- [A](a.md)", &[("a.md", unit("a", "[reference](https://example.com/paper#definition), [asset](diagram.svg), [mail](mailto:author@example.com)."))]);
    fs::write(fixture.0.join("md/diagram.svg"), "<svg></svg>").unwrap();
    let links = fixture.build().unwrap();
    let occurrences = &links.sources["a"].occurrences;
    assert_eq!(occurrences.len(), 3);
    assert!(
        matches!(&occurrences[0].target, LinkTarget::External { url } if url == "https://example.com/paper#definition")
    );
    assert!(
        matches!(&occurrences[1].target, LinkTarget::Asset { path } if path == "md/diagram.svg")
    );
    assert!(occurrences
        .iter()
        .all(|link| link.direction == Direction::External));
}

#[test]
fn mathjax_links_must_name_rendered_html_pages() {
    let fixture = Fixture::new(
        "- [A](a.md)\n- [B](b.md)",
        &[
            ("a.md", unit("a", r"\\(\href{b.md#claim-b}{B}\\)")),
            ("b.md", unit("b", "B.")),
        ],
    );
    let error = format!("{:#}", fixture.build().unwrap_err());
    assert!(
        error.contains("MathJax links must use the rendered .html"),
        "{error}"
    );
    assert!(error.contains("md/a.md:4"), "{error}");
}

#[test]
fn published_chapters_cannot_link_to_unpublished_html_targets() {
    let fixture = Fixture::new(
        "- [A](a.md)",
        &[
            ("a.md", unit("a", "[hidden](hidden.md#claim-hidden)")),
            ("hidden.md", unit("hidden", "A hidden definition.")),
        ],
    );
    let error = format!("{:#}", fixture.build().unwrap_err());
    assert!(
        error.contains("published chapter links to unpublished target"),
        "{error}"
    );
    assert!(error.contains("SUMMARY.md"), "{error}");
    fs::write(
        fixture.0.join("md/SUMMARY.md"),
        "- [A](a.md)\n- [Hidden](hidden.md)",
    )
    .unwrap();
    assert_eq!(
        fixture.build().unwrap().sources["a"].occurrences[0].direction,
        Direction::Forward
    );
}

use mdbook_dada::process;
use serde_json::{json, Value};
fn chapter(path: &str, content: &str) -> Value {
    json!({"Chapter":{"path":path,"content":content,"sub_items":[]}})
}
#[test]
fn indexes_forward_references_and_nested_chapters() {
    let mut book = json!({"sections":[chapter("intro.md","See {anchor-ref}`model.live`."),
        {"Chapter":{"path":"model/index.md","content":"{anchor}`model.live`\nLive objects.","sub_items":[chapter("model/details.md","See {anchor-ref}`model.live`.")]}}]});
    process(&mut book).unwrap();
    assert!(book["sections"][0]["Chapter"]["content"]
        .as_str()
        .unwrap()
        .contains("model/index.html#claim-model.live"));
    assert!(
        book["sections"][1]["Chapter"]["sub_items"][0]["Chapter"]["content"]
            .as_str()
            .unwrap()
            .contains("index.html#claim-model.live")
    );
}
#[test]
fn cross_references_traverse_to_parent_and_bad_references_fail() {
    let mut book = json!({"sections":[chapter("index.md","{anchor}`top`"),chapter("a/b.md","{anchor-ref}`top`")]});
    process(&mut book).unwrap();
    assert!(book.to_string().contains("../index.html#claim-top"));
    for entries in [
        vec![chapter("a.md", "{anchor-ref}`missing`")],
        vec![
            chapter("a.md", "{anchor}`x`"),
            chapter("b.md", "{anchor}`x`"),
        ],
        vec![chapter("a.md", "{anchor}`bad id`")],
    ] {
        assert!(process(&mut json!({"sections":entries})).is_err());
    }
}
#[test]
fn literal_examples_are_not_anchors() {
    let source="```text\n{anchor}`literal`\n```\n\n    {anchor}`indented`\n\n`{anchor}`literal\n\n\\{anchor}`escaped`\n\n<!-- {anchor}`comment` -->\n\n[{anchor}`linked`](https://example.com)\n";
    let mut book = json!({"sections":[chapter("a.md",source)]});
    process(&mut book).unwrap();
    assert_eq!(book["sections"][0]["Chapter"]["content"], source);
}
#[test]
fn heap_fences_render_and_preserve_source() {
    let mut book = json!({"sections":[chapter("a.md","Before.\n\n```{heap}\nvars = variables()\np = object(Point, \"α\")\nvars.p = owned(p)\n```\n\nAfter.")]});
    process(&mut book).unwrap();
    let text = book["sections"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(text.contains("<svg"));
    assert!(text.contains("aria-label=\"Diagram view\""));
    assert!(text.contains("value=\"rendered\" checked"));
    assert!(text.contains("class=\"heap-facts\""));
    assert!(text.contains("vars.p = owned(p)&#10;"));
    assert!(text.contains("Before."));
    assert!(text.contains("After."));
    assert!(!text.contains("```{heap}"));
}

#[test]
fn leading_declaration_shields_move_to_headers_without_losing_ids_or_body_markup() {
    use pulldown_cmark::{Event, Parser, Tag};

    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    for (kind, citation) in [
        ("definition", "Places:readSlot"),
        ("theorem", "Heap:deallocVariable_requires_top"),
        ("lemma", "Heap:deallocVariable_requires_top"),
        ("example", "Heap:integer_primitive"),
    ] {
        let source = format!(
            "```{{{kind}}} {citation}\n\n {{anchor}}`lookup`\n{{definition}}`second` **Statement.** See {{anchor-ref}}`lookup`.\n\n\\\\[S(p)=s\\\\]\n\n{{anchor}}`later` Details.\n```"
        );
        let mut book = json!({"items": [
            chapter("intro.md", "See {anchor-ref}`lookup`."),
            chapter("model/state.md", &source)
        ]});
        mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap();
        let output = book["items"][1]["Chapter"]["content"].as_str().unwrap();
        let (header, body) = output
            .split_once("<div class=\"lean-markdown-body\">")
            .unwrap();
        assert!(header.contains("<div class=\"block-heading\"><a id=\"claim-lookup\""));
        assert!(header.contains("id=\"claim-second\""));
        assert!(header.contains(&format!("aria-label=\"{kind}: lookup\"")));
        assert!(header.contains("class=\"view-options\""));
        assert!(!header.contains("class=\"block-label\""));
        assert_eq!(output.matches("id=\"claim-lookup\"").count(), 1);
        assert_eq!(output.matches("id=\"claim-second\"").count(), 1);
        assert!(body.contains("id=\"claim-later\""));
        assert!(body.contains("href=\"#claim-lookup\""));
        assert!(body.contains("<div class=\"math-display\">\\[S(p)=s\\]</div>"));
        assert!(Parser::new(output).any(|event| matches!(event, Event::Start(Tag::Strong))));
        assert!(book["items"][0]["Chapter"]["content"]
            .as_str()
            .unwrap()
            .contains("model/state.html#claim-lookup"));
    }
}

#[test]
fn nonheading_roles_and_nested_diagrams_stay_in_the_markdown_body() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    for prefix in [
        "Opening prose.\n\n{anchor}`body`",
        "{obligation}`body`",
        "{anchor-ref}`outside`\n\n{anchor}`body`",
        "`{anchor}`literal\n\n{anchor}`body`",
        "<!-- Heading comment. -->\n\n{anchor}`body`",
    ] {
        let source = format!(
            "{{anchor}}`outside`\n\n````{{definition}} Places:readSlot\n{prefix} Statement.\n\n```{{heap}}\nvars = variables()\nvars.x = uninitialized()\n```\n````"
        );
        let mut book = json!({"items": [chapter("state.md", &source)]});
        mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap();
        let output = book["items"][0]["Chapter"]["content"].as_str().unwrap();
        let (header, body) = output
            .split_once("<div class=\"lean-markdown-body\">")
            .unwrap();
        assert!(header.contains("<span class=\"block-label\">Definition</span>"));
        assert!(!header.contains("id=\"claim-body\""));
        assert!(body.contains("id=\"claim-body\""));
        assert!(body.contains("<span class=\"block-label\">Diagram</span>"));
        assert!(body.contains("<svg"));
        assert_eq!(output.matches("class=\"view-options\"").count(), 2);
    }
}

#[test]
fn unanchored_rendered_blocks_share_named_headers_and_grouped_choices() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    let radio_names = regex::Regex::new(r#"type="radio" name="([^"]+)""#).unwrap();
    for (kind, label, citation, body, alternate) in [
        (
            "definition",
            "Definition",
            "Places:readSlot",
            "Statement.",
            "Lean",
        ),
        (
            "theorem",
            "Theorem",
            "Heap:deallocVariable_requires_top",
            "Statement.",
            "Lean",
        ),
        (
            "lemma",
            "Lemma",
            "Heap:deallocVariable_requires_top",
            "Statement.",
            "Lean",
        ),
        (
            "example",
            "Example",
            "Heap:integer_primitive",
            "Statement.",
            "Lean",
        ),
        ("grammar", "Grammar", "Heap:Slot", "s ::= r", "Lean"),
        ("judgment", "Judgment", "Heap:Step", "S \\to S'", "Lean"),
        ("rule", "Rule", "Heap:Step.allocVariable", "P", "Lean"),
        ("heap", "Diagram", "", "vars = variables()", "Facts"),
    ] {
        let source = format!("```{{{kind}}} {citation}\n{body}\n```");
        let mut book = json!({"items": [chapter("state.md", &source)]});
        mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap();
        let output = book["items"][0]["Chapter"]["content"].as_str().unwrap();
        assert!(output.contains(&format!("aria-label=\"{label} view\"")));
        assert!(output.contains(&format!("<div class=\"block-heading\"><span class=\"block-label\">{label}</span></div><div class=\"view-options\">")));
        assert_eq!(output.matches("> Rendered</label>").count(), 1);
        assert_eq!(output.matches(&format!("> {alternate}</label>")).count(), 1);
        let names: Vec<_> = radio_names
            .captures_iter(output)
            .map(|capture| capture[1].to_owned())
            .collect();
        assert_eq!(names.len(), 2);
        assert_eq!(names[0], names[1]);
    }
}

#[test]
fn heading_anchors_do_not_replace_the_required_markdown_statement() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    let source = "```{definition} Places:readSlot\n{anchor}`lookup`\n{definition}`alias`\n```";
    let mut book = json!({"items": [chapter("state.md", source)]});
    let error = mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap_err();
    assert!(format!("{error:#}").contains("requires a Markdown body after its heading anchors"));
}

#[test]
fn header_selection_ignores_roles_inside_explicit_math() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    for prefix in ["", "{anchor}`lookup`\n"] {
        let source = format!(
            "```{{definition}} Places:readSlot\n{prefix}\\\\[\\text{{{{anchor}}`not an ID`}}\\\\]\n\n{{anchor}}`later` Statement.\n```"
        );
        let mut book = json!({"items": [chapter("state.md", &source)]});
        mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap();
        let output = book["items"][0]["Chapter"]["content"].as_str().unwrap();
        let (header, body) = output
            .split_once("<div class=\"lean-markdown-body\">")
            .unwrap();
        assert!(!header.contains("claim-later"));
        assert!(body.contains("id=\"claim-later\""));
        assert!(body.contains(r"\text{{anchor}`not an ID`}"));
        assert!(!output.contains("claim-not an ID"));
    }
}

#[test]
fn current_mdbook_schema_is_processed_and_unknown_schema_fails() {
    let mut book = json!({"items": [chapter("a.md", "{anchor}`a`\n\n{anchor-ref}`a`")]});
    process(&mut book).unwrap();
    assert!(book["items"][0]["Chapter"]["content"]
        .as_str()
        .unwrap()
        .contains("spec-shield"));
    assert!(process(&mut json!({"unexpected": []})).is_err());
}

// meta.syntax.anchors.inline and .literal
#[test]
fn inline_roles_preserve_paragraph_and_double_backticks_are_literal() {
    let source = "{anchor}`claim` This is the claim.\n\n{anchor}``example``";
    let mut book = json!({"items": [chapter("a.md", source)]});
    process(&mut book).unwrap();
    let output = book["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(output.contains("</a> This is the claim."));
    assert!(output.contains("{anchor}``example``"));
}

#[test]
fn informational_paragraphs_preserve_markdown_and_literal_examples() {
    let source = "{informational} Rationale with [a link](state.md) and *emphasis*.\n\n```text\n{informational} Literal.\n```";
    let mut book = json!({"items": [chapter("a.md", source)]});
    process(&mut book).unwrap();
    let output = book["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(output.contains("<span class=\"informational-label\">Informational</span> Rationale"));
    assert!(output.contains("[a link](state.md) and *emphasis*"));
    assert!(output.contains("{informational} Literal."));
}

#[test]
fn unlinked_example_labels_require_migration_but_literal_mentions_do_not() {
    let mut old = json!({"items": [chapter("a.md", "{example} `p.x` is a path.")]});
    assert!(format!("{:#}", process(&mut old).unwrap_err()).contains("has been replaced"));
    let source = "Mention {example} inline.\n\n```text\n{example} literal\n```";
    let mut book = json!({"items": [chapter("a.md", source)]});
    process(&mut book).unwrap();
    let text = book["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert_eq!(text, source);
    assert!(text.contains("Mention {example} inline."));
    assert!(text.contains("{example} literal"));
}

#[test]
fn linked_examples_preserve_native_markdown_and_select_one_lean_test() {
    use pulldown_cmark::{Event, Parser, Tag};

    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    let source = r"Before.

````{example} Heap:integer_primitive
**Create an integer.** See [the state](state.md).

1. Allocate `x`.
2. Create the value.

```text
createPrimitive(22, x)
```

After the operation, the payload is \\(22\\).
````

After.
";
    let mut book = json!({"items": [chapter("examples.md", source)]});
    mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap();
    let output = book["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(output.contains("aria-label=\"Example view\""));
    assert!(output.contains("Heap:integer_primitive"));
    assert!(output.contains("Step Int allocated (.createPrimitive 22 x) created"));
    assert!(!output.contains("createAggregate"));
    assert!(!output.contains("ANCHOR_END"));
    assert!(output.contains("<span class=\"math-inline\">&#92;&#40;22&#92;&#41;</span>"));
    // The HTML wrapper must leave the authored body to mdBook's Markdown parser.
    let events: Vec<_> = Parser::new(output).collect();
    assert!(events
        .iter()
        .any(|e| matches!(e, Event::Start(Tag::Strong))));
    assert!(events
        .iter()
        .any(|e| matches!(e, Event::Start(Tag::List(Some(1))))));
    assert!(events.iter().any(
        |e| matches!(e, Event::Start(Tag::Link { dest_url, .. }) if dest_url.as_ref() == "state.md")
    ));
    assert!(events
        .iter()
        .any(|e| matches!(e, Event::Start(Tag::CodeBlock(_)))));
    assert!(events
        .iter()
        .any(|e| matches!(e, Event::Text(text) if text.as_ref() == "After.")));

    let mut indented = json!({"items": [chapter("examples.md", "```{example} Heap:integer_primitive\n    createPrimitive(22, x)\n```")]});
    mdbook_dada::process_with_lean(&mut indented, Some(&root)).unwrap();
    let output = indented["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(Parser::new(output).any(|e| matches!(
        e,
        Event::Start(Tag::CodeBlock(pulldown_cmark::CodeBlockKind::Indented))
    )));
}

#[test]
fn linked_example_bodies_index_anchors_and_scope_nested_selectors() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    let example = r"````{example} Heap:nested_variables
See {anchor-ref}`outer`.

{anchor}`inner` The inner scope is removed.

```{heap}
vars = variables()
vars.x = uninitialized()
```

```{grammar} Heap:Slot
s ::= \bot
```
````";
    let mut book = json!({"items": [
        chapter("intro.md", "{anchor}`outer` See {anchor-ref}`inner`."),
        chapter("examples/scopes.md", example),
        chapter("examples/another.md", &example.replace("{anchor}`inner`", "{anchor-ref}`inner`"))
    ]});
    mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap();
    let text = book["items"][1]["Chapter"]["content"].as_str().unwrap();
    assert!(text.contains("../intro.html#claim-outer"));
    assert!(text.contains("id=\"claim-inner\""));
    assert!(text.contains("<svg"));
    assert!(text.contains("math-display"));
    assert!(book["items"][0]["Chapter"]["content"]
        .as_str()
        .unwrap()
        .contains("examples/scopes.html#claim-inner"));
    let all = book.to_string();
    let names: Vec<_> = regex::Regex::new(r#"type="radio" name="([^"]+)""#)
        .unwrap()
        .captures_iter(text)
        .map(|c| c[1].to_owned())
        .collect();
    assert_eq!(names.len(), 6);
    assert_eq!(
        names
            .iter()
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        3
    );
    assert!(all.contains("another.md"));

    let mut duplicate =
        json!({"items": [chapter("a.md", example), chapter("b.md", "{anchor}`inner`")]});
    assert!(format!(
        "{:#}",
        mdbook_dada::process_with_lean(&mut duplicate, Some(&root)).unwrap_err()
    )
    .contains("duplicate anchor"));
}

#[test]
fn linked_examples_fail_on_invalid_citations_bodies_or_nesting() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    for source in [
        "```{example}\nBody.\n```",
        "```{example}Heap:integer_primitive\nBody.\n```",
        "```{example} Heap:integer_primitive Heap:empty_array\nBody.\n```",
        "```{example} Heap:integer_primitive\n  \n```",
        "```{example} Heap:missing\nBody.\n```",
        "```{example} Heap:Step\nBody.\n```",
        "```{example} ../Heap:integer_primitive\nBody.\n```",
        "````{example} Heap:integer_primitive\n```{example} Heap:empty_array\nNested.\n```\n````",
    ] {
        let mut book = json!({"items": [chapter("examples.md", source)]});
        let error = mdbook_dada::process_with_lean(&mut book, Some(&root)).expect_err(source);
        assert!(format!("{error:#}").contains("examples.md"), "{source}");
    }
    let mut missing_root = json!({"items": [chapter("examples.md", "```{example} Heap:integer_primitive\nBody.\n```")]});
    assert!(process(&mut missing_root).is_err());
    let literal = "````text\n```{example} Missing:nope\nLiteral.\n```\n````\n\n    ```{example} Missing:nope\n    Literal.\n    ```";
    let mut book = json!({"items": [chapter("examples.md", literal)]});
    process(&mut book).unwrap();
    assert_eq!(book["items"][0]["Chapter"]["content"], literal);
}

#[test]
fn authored_grammar_keeps_math_and_groups_citations_in_order() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    let source = r"```{grammar} Heap:Slot Heap.lean:Object
\begin{aligned}
s &::= \bot \mid r \\
o &::= p \mid \{f \mapsto s\} \mid {\overline s}
\end{aligned}
```";
    let mut book = json!({"items": [chapter("state.md", source)]});
    mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap();
    let html = book["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(html.contains(r"s &amp;::= \bot \mid r"));
    assert!(html.contains(r"o &amp;::= p \mid \{f \mapsto s\} \mid {\overline s}"));
    assert!(html.find("Heap:Slot").unwrap() < html.find("Heap.lean:Object").unwrap());
    let lean = html.split("class=\"lean-source\"").nth(1).unwrap();
    assert!(lean.find("Slot").unwrap() < lean.find("Object").unwrap());
    assert!(lean.contains("| uninitialized"));
    assert!(lean.contains("| array"));
    assert!(lean.contains("lean-keyword"));
    assert_eq!(html.matches("class=\"lean-selector\"").count(), 1);
    assert_eq!(html.matches("> Rendered</label>").count(), 1);
    assert_eq!(html.matches("> Lean</label>").count(), 1);
    let rendered = html.split("class=\"lean-source\"").next().unwrap();
    assert!(!rendered.contains("uniqueKeys"));
    assert!(!rendered.contains("FiniteMap"));
}

#[test]
fn authored_grammar_accepts_single_citations_and_escapes_html() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    let source = r"```{grammar} Heap:ObjectId
\text{chosen by author} & a < b > c \quad ${uninterpreted}
```";
    let mut book = json!({"items": [chapter("state.md", source)]});
    mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap();
    let html = book["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(html.contains(r"\text{chosen by author} &amp; a &lt; b &gt; c \quad ${uninterpreted}"));
    assert!(!html.contains("a < b > c"));
    assert!(html.contains("ObjectId"));
    assert!(html.contains("index : Nat"));
}

#[test]
fn authored_grammar_rejects_invalid_citations_and_missing_bodies() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    for target in [
        "Missing:Place",
        "Heap:Missing",
        "Heap:Step.allocVariable",
        "Heap:allocVariable_contents",
        "../Heap:Place",
        "Heap:Object Heap:Missing",
    ] {
        let mut book =
            json!({"items": [chapter("state.md", &format!("```{{grammar}} {target}\nP\n```"))]});
        let error = mdbook_dada::process_with_lean(&mut book, Some(&root)).expect_err(target);
        assert!(format!("{error:#}").contains("state.md"), "{target}");
    }
    for source in [
        "```{grammar} Heap:Object\n```",
        "```{grammar} Heap:Object\n  \n```",
        "```{grammar}Heap:Object\nP\n```",
    ] {
        let mut book = json!({"items": [chapter("state.md", source)]});
        let error = mdbook_dada::process_with_lean(&mut book, Some(&root)).expect_err(source);
        assert!(format!("{error:#}").contains("state.md"), "{source}");
    }
    let mut book = json!({"items": [chapter("state.md", "```{grammar} Heap:Slot\ns ::= r\n```")]});
    assert!(
        process(&mut book).is_err(),
        "Lean citations require a source root"
    );
}

#[test]
fn block_directives_are_distinct_from_literal_code_and_inline_roles() {
    let literal =
        "```heap\nnot facts\n```\n\n```grammar\nnot grammar\n```\n\n```lean\nnot lean\n```\n\n```text\n{lean.type}`Missing:Place`\n```";
    let mut book = json!({"items": [chapter("a.md", literal)]});
    process(&mut book).unwrap();
    assert_eq!(book["items"][0]["Chapter"]["content"], literal);
    let mut old = json!({"items": [chapter("a.md", "{lean.type}`Heap:Place`")]});
    let error = process(&mut old).unwrap_err();
    assert!(format!("{error:#}").contains("lean.type"));
}

#[test]
fn generated_grammar_directives_require_migration() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    for source in [
        "```{lean.type}\nHeap:Place\n```",
        "```{grammar}\nSlot = Empty | Ref(target: Id);\n```",
    ] {
        let mut book = json!({"items": [chapter("state.md", source)]});
        let error = mdbook_dada::process_with_lean(&mut book, Some(&root)).expect_err(source);
        let message = format!("{error:#}");
        assert!(message.contains("state.md"));
        assert!(message.contains("grammar"), "{source}: {message}");
        assert!(message.contains("authored LaTeX"), "{source}: {message}");
    }
}

// Authored mathematics is presented alongside a checked source selection; the
// preprocessor does not establish that the two representations correspond.
#[test]
fn authored_judgments_and_rules_keep_tex_and_show_cited_source() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    let source = r"```{judgment} Heap:Step
S \xrightarrow{op} S'
```

```{rule} Heap.lean:Step.allocVariable
\frac{\mathrm{authorPremise}}{\mathrm{authorConclusion}}
```
";
    let mut book = json!({"items": [chapter("ops.md", source)]});
    mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap();
    let html = book["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(html.contains(r"S \xrightarrow{op} S&#39;"));
    assert!(html.contains(r"\frac{\mathrm{authorPremise}}{\mathrm{authorConclusion}}"));
    assert!(html.contains("Heap:Step"));
    assert!(html.contains("Heap.lean:Step.allocVariable"));
    assert!(html.contains("| allocVariable"));
    let selected_rule = html.rsplit("class=\"lean-source\"").next().unwrap();
    assert!(selected_rule.contains("| allocVariable"));
    assert!(!selected_rule.contains("| deallocVariable"));
    assert_eq!(html.matches("class=\"lean-selector\"").count(), 2);
    assert_eq!(html.matches("> Rendered</label>").count(), 2);
    assert_eq!(html.matches("> Lean</label>").count(), 2);

    // Each selector's two choices share a group, but different blocks do not.
    let names: Vec<_> = regex::Regex::new(r#"type="radio" name="([^"]+)""#)
        .unwrap()
        .captures_iter(html)
        .map(|captures| captures[1].to_owned())
        .collect();
    assert_eq!(names.len(), 4);
    assert_eq!(names[0], names[1]);
    assert_eq!(names[2], names[3]);
    assert_ne!(names[0], names[2]);

    // Selecting either a middle or final case must exclude its neighbors, even
    // when the judgment and operation have an explicit Primitive parameter.
    let cases = [
        "allocVariable",
        "deallocVariable",
        "createPrimitive",
        "createAggregate",
        "createArray",
    ];
    for case in cases {
        let source = format!("```{{rule}} Heap:Step.{case}\nP\n```");
        let mut book = json!({"items": [chapter("ops.md", &source)]});
        mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap();
        let html = book["items"][0]["Chapter"]["content"].as_str().unwrap();
        assert!(html.contains("Operation Primitive"));
        for candidate in cases {
            assert_eq!(
                html.contains(&format!("| {candidate}")),
                candidate == case,
                "case {case} must select only its own constructor"
            );
        }
    }
}

#[test]
fn authored_math_escapes_html_without_interpreting_placeholders() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    let source = r"```{rule} Heap:Step.allocVariable
\frac{a < b & c > d}{${authorChosenName}}
```
";
    let mut book = json!({"items": [chapter("ops.md", source)]});
    mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap();
    let html = book["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(html.contains(r"\frac{a &lt; b &amp; c &gt; d}{${authorChosenName}}"));
    assert!(!html.contains("a < b & c > d"));
    let rendered = html.split("class=\"lean-source\"").next().unwrap();
    assert!(!rendered.contains(r"\xrightarrow"));
    assert!(!rendered.contains("insertFresh"));
}

#[test]
fn authored_theorems_show_the_exact_named_statement_and_proof() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    let source = r"```{theorem} Heap.lean:deallocVariable_requires_top
A successful deallocation removes the top slot.

\\[
S \xrightarrow{\mathsf{deallocVariable}(x)} S' \implies \operatorname{top}(V) = x
\\]

**Proof outline.** Inspect the deallocation constructor's top-slot premise.
```";
    let mut book = json!({"items": [chapter("invariants.md", source)]});
    mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap();
    let html = book["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(html.contains(r"\implies \operatorname{top}(V) = x"));
    assert!(html.contains("Heap.lean:deallocVariable_requires_top"));
    assert!(html.contains("lean-keyword\">theorem</span> deallocVariable_requires_top"));
    assert!(html.contains("cases step"));
    assert!(!html.contains("theorem</span> deallocVariable_pops"));
    assert_eq!(html.matches("class=\"lean-selector\"").count(), 1);
    assert_eq!(html.matches("> Rendered</label>").count(), 1);
    assert_eq!(html.matches("> Lean</label>").count(), 1);
}

#[test]
fn authored_theorems_select_literal_qualified_names() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    let source = r"```{theorem} Moves:MoveReference.dependent_follows
Dependent leases follow the reference.

\\[P \implies Q\\]
```";
    let mut book = json!({"items": [chapter("moves.md", source)]});
    mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap();
    let html = book["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(html.contains("Moves:MoveReference.dependent_follows"));
    assert!(html.contains("lean-keyword\">theorem</span> MoveReference.dependent_follows"));
    assert!(html.contains("move.other_references"));
    assert!(!html.contains("theorem</span> MoveReference.other_references"));
    for citation in [
        "Moves:Dada.Heap.MoveReference.dependent_follows",
        "Moves:MoveReference..dependent_follows",
        "Moves:.MoveReference.dependent_follows",
        "Moves:MoveReference.dependent_follows.",
    ] {
        let source = format!("```{{theorem}} {citation}\nP\n```");
        let mut book = json!({"items": [chapter("moves.md", &source)]});
        assert!(mdbook_dada::process_with_lean(&mut book, Some(&root)).is_err());
    }
}

#[test]
fn authored_theorems_reject_wrong_kinds_and_malformed_directives() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    for source in [
        "```{theorem}\nP\n```",
        "```{theorem}Heap:deallocVariable_requires_top\nP\n```",
        "```{theorem} Heap:deallocVariable_requires_top Heap:deallocVariable_pops\nP\n```",
        "```{theorem} Heap:deallocVariable_requires_top\n \n```",
        "```{theorem} Heap:Step\nP\n```",
        "```{theorem} Heap:Step.allocVariable\nP\n```",
        "```{theorem} Heap:integer_primitive\nP\n```",
        "```{theorem} Heap:initialFields\nP\n```",
        "```{theorem} Heap:missing\nP\n```",
        "```{theorem} Missing:theorem\nP\n```",
        "```{theorem} ../Heap:deallocVariable_requires_top\nP\n```",
    ] {
        let mut book = json!({"items": [chapter("invariants.md", source)]});
        let error = mdbook_dada::process_with_lean(&mut book, Some(&root)).expect_err(source);
        assert!(format!("{error:#}").contains("invariants.md"), "{source}");
    }
    let mut missing_root = json!({"items": [chapter("invariants.md", "```{theorem} Heap:deallocVariable_requires_top\nP\n```")]});
    assert!(process(&mut missing_root).is_err());
    let literal = "````text\n```{theorem} Missing:nope\nP\n```\n````";
    let mut book = json!({"items": [chapter("invariants.md", literal)]});
    process(&mut book).unwrap();
    assert_eq!(book["items"][0]["Chapter"]["content"], literal);
}

#[test]
fn authored_math_requires_one_opening_argument_and_a_body() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    for source in [
        "```{rule}\nHeap:Step.allocVariable\n\\frac{P}{Q}\n```",
        "```{judgment}\nHeap:Step\nS \\to S'\n```",
        "```{rule} Heap:Step.allocVariable\n```",
        "```{judgment} Heap:Step\n  \n```",
        "```{rule} Heap:Step.allocVariable Heap:Step.allocVariable\nP\n```",
        "```{judgment}Heap:Step\nP\n```",
    ] {
        let mut book = json!({"items": [chapter("ops.md", source)]});
        let error = mdbook_dada::process_with_lean(&mut book, Some(&root)).expect_err(source);
        assert!(format!("{error:#}").contains("ops.md"), "{source}");
    }
    let mut book =
        json!({"items": [chapter("ops.md", "```{rule} Heap:Step.allocVariable\nP\n```")]});
    assert!(
        process(&mut book).is_err(),
        "Lean selection requires a source root"
    );
}

#[test]
fn authored_math_rejects_missing_or_wrong_kind_source_selections() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    for (kind, target) in [
        ("judgment", "Missing:Step"),
        ("judgment", "Heap:Missing"),
        ("judgment", "Heap:VariableId"),
        ("rule", "Heap:Step.missing"),
        ("rule", "Heap:Step"),
        ("rule", "Heap:VariableId.index"),
        ("rule", "../Heap:Step.allocVariable"),
    ] {
        let mut book =
            json!({"items": [chapter("ops.md", &format!("```{{{kind}}} {target}\nP\n```"))]});
        let error = mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap_err();
        let message = format!("{error:#}");
        assert!(message.contains("ops.md"), "{kind} {target}");
        if target.starts_with("Heap:VariableId") {
            assert!(
                message.contains("must select inductive declarations"),
                "{kind} {target}: {message}"
            );
        }
    }
}

#[test]
fn authored_directive_examples_remain_literal_inside_other_code() {
    let source = r"````text
```{rule} Missing:J.r
P
```
```{judgment} Missing:J
Q
```
```{grammar} Missing:T Missing:U
T ::= U
```
```{grammar}
Legacy = Constructor;
```
```{lean.type}
Missing:T
```
````

    ```{rule} Missing:J.r
    P
    ```

```rule
Missing:J.r
```
";
    let mut book = json!({"items": [chapter("ops.md", source)]});
    process(&mut book).unwrap();
    assert_eq!(book["items"][0]["Chapter"]["content"], source);
}

#[test]
fn inferred_judgment_and_rule_directives_require_migration() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    for (kind, target) in [
        ("judgment", "Heap:Step"),
        ("rule", "Heap:Step.allocVariable"),
    ] {
        let source = format!("```{{lean.{kind}}}\n{target}\n```");
        let mut book = json!({"items": [chapter("ops.md", &source)]});
        let error = mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap_err();
        let message = format!("{error:#}");
        assert!(message.contains(&format!("lean.{kind}")));
        assert!(message.contains(&format!("{{{kind}}}")));
        assert!(message.contains("ops.md"));
    }
}

#[test]
fn theorem_and_lemma_bodies_preserve_markdown_math_and_proof_outlines() {
    use pulldown_cmark::{Event, Parser, Tag};
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    for (kind, label) in [("theorem", "Theorem"), ("lemma", "Lemma")] {
        let source = format!(
            r"````{{{kind}}} Heap:deallocVariable_requires_top
{{anchor}}`top-slot` A successful deallocation removes the **top** slot.

\\[
S \xrightarrow{{\mathsf{{deallocVariable}}(x)}} S' \implies \operatorname{{top}}(V)=x
\\]

**Proof outline.**

1. Inspect the [transition rule](operations.md).
2. Use its `top` premise.

```lean
cases step
```
````

After the proof."
        );
        let mut book = json!({"items": [chapter("proofs.md", &source)]});
        mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap();
        let output = book["items"][0]["Chapter"]["content"].as_str().unwrap();
        assert!(output.contains(&format!("aria-label=\"{label} view\"")));
        assert!(!output.contains("class=\"block-label\""));
        assert!(output.contains(&format!("aria-label=\"{kind}: top-slot\"")));
        assert!(output.contains("lean-keyword\">theorem</span> deallocVariable_requires_top"));
        assert_eq!(output.matches("class=\"math-display\"").count(), 1);
        assert!(output.contains(r"\["));
        assert!(output.contains(r"\]"));
        let events: Vec<_> = Parser::new(output).collect();
        assert!(events
            .iter()
            .any(|e| matches!(e, Event::Start(Tag::Strong))));
        assert!(events
            .iter()
            .any(|e| matches!(e, Event::Start(Tag::List(Some(1))))));
        assert!(events
            .iter()
            .any(|e| matches!(e, Event::Start(Tag::CodeBlock(_)))));
        assert!(events.iter().any(|e| matches!(e, Event::Start(Tag::Link { dest_url, .. }) if dest_url.as_ref() == "operations.md")));
        assert!(events
            .iter()
            .any(|e| matches!(e, Event::Text(text) if text.as_ref() == "After the proof.")));
    }
}

#[test]
fn definition_blocks_select_multiple_complete_declarations_and_preserve_markdown() {
    use pulldown_cmark::{Event, Parser, Tag};
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    let source = r"````{definition} Places:readSlot Invariants:Stored Invariants:AllocatedObject Heap:State.initial Heap:FieldName Heap:VariableId Heap:Slot
{anchor}`slot-lookup` Write **lookup** as \\(S(p)=s\\).

\\[
S(p)=s \iff \mathsf{readSlot}(S,p)=\mathsf{some}(s)
\\]

1. A variable selects a slot.
2. A missing place has no slot.

```{grammar} Heap:Place
p ::= x
```
````";
    let input = json!({"items": [
        chapter("state.md", source),
        chapter("operations.md", "See {anchor-ref}`slot-lookup`."),
    ]});
    let mut first = input.clone();
    let mut second = input;
    mdbook_dada::process_with_lean(&mut first, Some(&root)).unwrap();
    mdbook_dada::process_with_lean(&mut second, Some(&root)).unwrap();
    assert_eq!(first, second, "selectors must be deterministic");
    let output = first["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(output.contains("aria-label=\"Definition view\""));
    assert!(!output.contains("class=\"block-label\">Definition</span>"));
    assert!(output.contains("aria-label=\"definition: slot-lookup\""));
    assert!(output.contains("lean-keyword\">def</span> readSlot"));
    assert!(output.contains("elements[index]?"));
    assert!(!output.contains("def</span> writeSlot"));
    assert!(!output.contains("A write never creates"));
    assert!(output.contains("lean-keyword\">def</span> Stored"));
    assert!(output.contains("lean-keyword\">def</span> AllocatedObject"));
    assert!(output.contains("lean-keyword\">def</span> State.initial"));
    assert!(output.contains("lean-keyword\">abbrev</span> FieldName"));
    assert!(output.contains("lean-keyword\">structure</span> VariableId"));
    assert!(output.contains("lean-keyword\">inductive</span> Slot"));
    assert_eq!(output.matches("class=\"math-display\"").count(), 2);
    assert!(output.contains("class=\"math-inline\""));
    let events: Vec<_> = Parser::new(output).collect();
    assert!(events
        .iter()
        .any(|event| matches!(event, Event::Start(Tag::Strong))));
    assert!(events
        .iter()
        .any(|event| matches!(event, Event::Start(Tag::List(Some(1))))));
    assert!(first["items"][1]["Chapter"]["content"]
        .as_str()
        .unwrap()
        .contains("state.html#claim-slot-lookup"));
    let mut duplicate = json!({"items": [chapter("state.md", source), chapter("other.md", "{obligation}`slot-lookup`")]});
    assert!(format!(
        "{:#}",
        mdbook_dada::process_with_lean(&mut duplicate, Some(&root)).unwrap_err()
    )
    .contains("duplicate anchor"));
}

#[test]
fn definition_blocks_reject_missing_wrong_kind_and_malformed_citations() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    for source in [
        "```{definition}\nBody.\n```",
        "```{definition}Heap:State\nBody.\n```",
        "```{definition} Heap:State\n \n```",
        "```{definition} Heap:deallocVariable_requires_top\nBody.\n```",
        "```{definition} Heap:integer_primitive\nBody.\n```",
        "```{definition} Heap:Step.allocVariable\nBody.\n```",
        "```{definition} Heap:State Heap:missing\nBody.\n```",
        "```{definition} ../Heap:State\nBody.\n```",
        "```{definition} Missing:State\nBody.\n```",
    ] {
        let mut book = json!({"items": [chapter("state.md", source)]});
        let error = mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap_err();
        assert!(format!("{error:#}").contains("state.md"), "{source}");
    }
    let mut no_root =
        json!({"items": [chapter("state.md", "```{definition} Heap:State\nBody.\n```")]});
    assert!(process(&mut no_root).is_err());
    let literal = "````text\n```{definition} Missing:nope\nBody.\n```\n````\n\n    ```{definition} Missing:nope\n    Body.\n    ```";
    let mut book = json!({"items": [chapter("literal.md", literal)]});
    process(&mut book).unwrap();
    assert_eq!(book["items"][0]["Chapter"]["content"], literal);
}

#[test]
fn proof_blocks_index_cross_chapter_anchors_and_scope_supported_nested_blocks() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    let proof = r"````{lemma} Heap:deallocVariable_requires_top
{anchor}`top` See {anchor-ref}`state`.

```{grammar} Heap:Slot
s ::= \bot
```

```{heap}
vars = variables()
vars.x = uninitialized()
```
````";
    let input = json!({"items": [
        chapter("state.md", "{definition}`state` See {anchor-ref}`top`."),
        chapter("proofs/top.md", proof),
        chapter("proofs/other.md", &proof.replace("{anchor}`top`", "{anchor-ref}`top`")),
    ]});
    let mut first = input.clone();
    let mut second = input;
    mdbook_dada::process_with_lean(&mut first, Some(&root)).unwrap();
    mdbook_dada::process_with_lean(&mut second, Some(&root)).unwrap();
    assert_eq!(first, second, "selector IDs must be deterministic");
    let state = first["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(state.contains("proofs/top.html#claim-top"));
    let proof = first["items"][1]["Chapter"]["content"].as_str().unwrap();
    assert!(proof.contains("../state.html#claim-state"));
    assert!(proof.contains("aria-label=\"lemma: top\""));
    assert!(proof.contains("math-display"));
    assert!(proof.contains("<svg"));
    let radios = regex::Regex::new(r#"type="radio" name="([^"]+)""#).unwrap();
    let names: Vec<_> = first["items"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|chapter| {
            radios
                .captures_iter(chapter["Chapter"]["content"].as_str().unwrap())
                .map(|capture| capture[1].to_owned())
                .collect::<Vec<_>>()
        })
        .collect();
    assert_eq!(names.len(), 12);
    assert_eq!(
        names
            .iter()
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        6
    );

    let mut duplicate = json!({"items": [
        chapter("proof.md", "```{lemma} Heap:deallocVariable_requires_top\n{anchor}`top` Statement.\n```"),
        chapter("other.md", "{obligation}`top`"),
    ]});
    assert!(format!(
        "{:#}",
        mdbook_dada::process_with_lean(&mut duplicate, Some(&root)).unwrap_err()
    )
    .contains("duplicate anchor"));
}

#[test]
fn markdown_proof_blocks_reject_invalid_targets_and_all_nested_proof_kinds() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    for kind in ["theorem", "lemma"] {
        for citation in [
            "",
            "Heap:Step",
            "Heap:Step.allocVariable",
            "Heap:initialFields",
            "Heap:integer_primitive",
            "Heap:missing",
            "Missing:proof",
            "../Heap:deallocVariable_requires_top",
            "Heap:deallocVariable_requires_top Heap:deallocVariable_pops",
        ] {
            let source = format!("```{{{kind}}} {citation}\nClaim.\n```");
            let mut book = json!({"items": [chapter("proofs.md", &source)]});
            assert!(
                mdbook_dada::process_with_lean(&mut book, Some(&root)).is_err(),
                "{source}"
            );
        }
        for source in [
            format!("```{{{kind}}}Heap:deallocVariable_requires_top\nClaim.\n```"),
            format!("```{{{kind}}} Heap:deallocVariable_requires_top\n \n```"),
        ] {
            let mut book = json!({"items": [chapter("proofs.md", &source)]});
            assert!(
                mdbook_dada::process_with_lean(&mut book, Some(&root)).is_err(),
                "{source}"
            );
        }
    }
    let targets = [
        ("definition", "Places:readSlot"),
        ("example", "Heap:integer_primitive"),
        ("theorem", "Heap:deallocVariable_requires_top"),
        ("lemma", "Heap:deallocVariable_requires_top"),
    ];
    for (outer, outer_target) in targets {
        for (inner, inner_target) in targets {
            let source = format!(
                "````{{{outer}}} {outer_target}\n```{{{inner}}} {inner_target}\nNested.\n```\n````"
            );
            let mut book = json!({"items": [chapter("proofs.md", &source)]});
            let error = mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap_err();
            assert!(
                format!("{error:#}").contains("cannot be nested"),
                "{source}"
            );
        }
    }
    let literal = "````text\n```{lemma} Missing:nope\nLiteral.\n```\n````";
    let mut book = json!({"items": [chapter("proofs.md", literal)]});
    process(&mut book).unwrap();
    assert_eq!(book["items"][0]["Chapter"]["content"], literal);
}

#[test]
fn proof_markdown_is_linted_with_original_chapter_lines() {
    for kind in ["definition", "theorem", "lemma"] {
        let source = format!(
            "# Proof\n\n```{{{kind}}} Heap:deallocVariable_requires_top\nBad \\overline x.\n```"
        );
        let mut book = json!({"items": [chapter("proofs.md", &source)]});
        let error = process(&mut book).unwrap_err().to_string();
        assert!(error.contains("proofs.md:4:"), "{error}");
    }
}

#[test]
fn typed_anchor_roles_share_ids_and_references_without_implying_proofs() {
    let mut book = json!({"items": [
        chapter("index.md", "{anchor}`navigation` See {anchor-ref}`state` and {anchor-ref}`safety`."),
        chapter("model/state.md", "{definition}`state` State components.\n\n{obligation}`safety` This property has no proof yet."),
    ]});
    process(&mut book).unwrap();
    let intro = book["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(intro.contains("aria-label=\"anchor: navigation\""));
    assert!(intro.contains("model/state.html#claim-state"));
    assert!(intro.contains("model/state.html#claim-safety"));
    let body = book["items"][1]["Chapter"]["content"].as_str().unwrap();
    assert!(body.contains("aria-label=\"definition: state\""));
    assert!(body.contains("aria-label=\"proof obligation: safety\""));
    assert!(!body.contains("lean-selector"));
    assert!(!body.contains("Theorem"));
    for first in ["anchor", "definition", "obligation"] {
        for second in ["anchor", "definition", "obligation"] {
            let mut duplicate = json!({"items": [
                chapter("a.md", &format!("{{{first}}}`same`")),
                chapter("b.md", &format!("{{{second}}}`same`")),
            ]});
            assert!(
                format!("{:#}", process(&mut duplicate).unwrap_err()).contains("duplicate anchor")
            );
        }
    }
    let literal = "```text\n{definition}`duplicate`\n{obligation}`duplicate`\n```\n\n{definition}``double``\n\n\\{obligation}`escaped`";
    let mut book = json!({"items": [chapter("literal.md", literal)]});
    process(&mut book).unwrap();
    assert_eq!(book["items"][0]["Chapter"]["content"], literal);
}

#[test]
fn explicit_math_survives_markdown_and_smart_punctuation_in_prose_and_proof_bodies() {
    use pulldown_cmark::{Event, Options, Parser};
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    let formula = r"\frac{S'=S[p\mapsto s]}{S'(q)=\begin{cases}s&q=p\\S(q)&q\ne p\end{cases}}";
    let body = format!(
        "**Statement.** The result is \\\\(S'_x \\ne S_x\\\\).\n\n\\\\[\n{formula}\n\\\\]\n\n**Proof outline.** Apply the rule."
    );
    for opening in [
        None,
        Some("{example} Heap:integer_primitive"),
        Some("{definition} Places:readSlot"),
        Some("{theorem} Heap:deallocVariable_requires_top"),
        Some("{lemma} Heap:deallocVariable_requires_top"),
    ] {
        let source = opening.map_or_else(|| body.clone(), |info| format!("```{info}\n{body}\n```"));
        let mut book = json!({"items": [chapter("proofs.md", &source)]});
        mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap();
        let markdown = book["items"][0]["Chapter"]["content"].as_str().unwrap();
        let events: Vec<_> = Parser::new_ext(markdown, Options::ENABLE_SMART_PUNCTUATION).collect();
        let rendered: String = events
            .iter()
            .filter_map(|event| match event {
                Event::Text(text) | Event::Html(text) | Event::InlineHtml(text) => {
                    Some(text.as_ref())
                }
                _ => None,
            })
            .collect();
        assert!(
            rendered.contains(&format!(
                "<div class=\"math-display\">\\[&#10;{}&#10;\\]</div>",
                mdbook_dada::escape(formula)
            )),
            "{rendered}"
        );
        assert!(
            rendered.contains("<span class=\"math-inline\">\\(S'_x \\ne S_x\\)</span>"),
            "{rendered}"
        );
        assert!(rendered.contains("Statement."));
        assert!(rendered.contains("Proof outline."));
        assert!(!rendered.contains('’'));
    }
}

#[test]
fn explicit_math_is_literal_in_code_links_and_html_and_does_not_define_roles() {
    let literal = r"```text
\\[
S' \\ T
\\]
```

    \\(S'_x\\)

`\\(S'\\)` and [\\(S'\\)](somewhere.md).

<pre>\\[S'\\]</pre>

Escaped \\\(S'\\).
";
    let mut book = json!({"items": [chapter("literal.md", literal)]});
    process(&mut book).unwrap();
    assert_eq!(book["items"][0]["Chapter"]["content"], literal);
    let mut math = json!({"items": [chapter("math.md", r"\\[\text{{anchor}`literal`}\\] \n\\(\text{{definition}`literal`}\\)")]});
    process(&mut math).unwrap();
    let output = math["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(output.contains("math-display"));
    assert!(output.contains("math-inline"));
    assert!(!output.contains("spec-shield"));
}

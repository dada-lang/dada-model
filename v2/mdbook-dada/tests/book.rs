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
    assert!(output.contains(r"\\(22\\)"));
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

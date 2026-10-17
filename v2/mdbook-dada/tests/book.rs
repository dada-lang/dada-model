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
    let mut book = json!({"sections":[chapter("a.md","Before.\n\n```{heap}\nmain = frame()\np = object(Point, \"α\")\nmain.p = owned(p)\n```\n\nAfter.")]});
    process(&mut book).unwrap();
    let text = book["sections"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(text.contains("<svg"));
    assert!(text.contains("aria-label=\"Diagram view\""));
    assert!(text.contains("value=\"rendered\" checked"));
    assert!(text.contains("class=\"heap-facts\""));
    assert!(text.contains("main.p = owned(p)&#10;"));
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

// meta.syntax.grammar.rendering: actual fenced blocks render; literal examples stay literal.
#[test]
fn grammar_fences_render_and_errors_include_chapter() {
    let mut book = json!({"items": [chapter("state.md", "```{grammar}\nSlot = Empty | Ref(target: Id);\n```\n\n````text\n```{grammar}\nnot a definition\n```\n````")]});
    process(&mut book).unwrap();
    let output = book["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(output.contains("grammar-definition"));
    assert!(output.contains("not a definition"));
    assert!(output.contains("<code>| Ref(target: Id)</code>"));
    let mut bad = json!({"items": [chapter("state.md", "```{grammar}\nSlot = Ref(target);\n```")]});
    let error = process(&mut bad).unwrap_err();
    assert!(format!("{error:#}").contains("chapter state.md"));
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
fn example_labels_leave_code_and_inline_mentions_literal() {
    let source = "{example} `main: p.x` is a path.\n\nMention {example} inline.\n\n```text\n{example} literal\n```";
    let mut book = json!({"items": [chapter("a.md", source)]});
    process(&mut book).unwrap();
    let text = book["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(text.contains("<span class=\"example-label\">Example</span> `main: p.x`"));
    assert!(text.contains("Mention {example} inline."));
    assert!(text.contains("{example} literal"));
}

#[test]
fn lean_inclusion_reads_actual_source_and_rejects_missing_targets() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    let mut book = json!({"items": [chapter("state.md", "```{lean.type}\nHeap:Place\n```\n\n```text\n{lean.type}`Missing:Place`\n```")]});
    mdbook_dada::process_with_lean(&mut book, Some(&root)).unwrap();
    let output = book["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(output.contains("lean-keyword"));
    assert!(output.contains("| element"));
    assert!(output.contains("{lean.type}`Missing:Place`"));
    for target in ["Missing:Place", "Heap:Missing", "../Heap:Place"] {
        let mut book =
            json!({"items": [chapter("state.md", &format!("```{{lean.type}}\n{target}\n```"))]});
        assert!(mdbook_dada::process_with_lean(&mut book, Some(&root)).is_err());
    }
}

#[test]
fn block_directives_are_distinct_from_literal_code_and_inline_roles() {
    let literal =
        "```heap\nnot facts\n```\n\n```grammar\nnot grammar\n```\n\n```lean\nnot lean\n```";
    let mut book = json!({"items": [chapter("a.md", literal)]});
    process(&mut book).unwrap();
    assert_eq!(book["items"][0]["Chapter"]["content"], literal);
    let mut old = json!({"items": [chapter("a.md", "{lean.type}`Heap:Place`")]});
    assert!(process(&mut old).is_err());
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../lean");
    let mut group = json!({"items": [chapter("a.md", "```{lean.type}\nHeap:FrameId\nHeap:ObjectId\nHeap:FiniteMap\n```")]});
    mdbook_dada::process_with_lean(&mut group, Some(&root)).unwrap();
    let html = group["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert!(html.find("FrameId").unwrap() < html.find("ObjectId").unwrap());
    assert!(html.contains("uniqueKeys"));
    assert_eq!(html.matches("class=\"lean-selector\"").count(), 1);
    let mut empty = json!({"items": [chapter("a.md", "```{lean.type}\n\n```")]});
    assert!(mdbook_dada::process_with_lean(&mut empty, Some(&root)).is_err());
}

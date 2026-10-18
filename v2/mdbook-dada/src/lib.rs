//! Presentation-only mdBook processing. Associations are not verification evidence.
pub mod graph;
pub mod lean;
pub mod lint;
mod routing;

use anyhow::{bail, ensure, Context, Result};
use pulldown_cmark::{CodeBlockKind, Event, Parser, Tag, TagEnd};
use regex::Regex;
use serde_json::Value;
use std::{collections::BTreeMap, ops::Range, path::Path};

pub fn escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
        .replace('\'', "&#39;")
}

#[derive(Debug)]
struct Role {
    range: Range<usize>,
    id: String,
    definition: bool,
    lean: bool,
}

// Use Markdown's source ranges to recognize roles, leaving code examples, links,
// escaped text, and HTML blocks alone. The role body is a single-backtick code span.
fn roles(source: &str) -> Result<Vec<Role>> {
    let id_pattern = Regex::new(r"^[A-Za-z0-9][A-Za-z0-9_.-]*$")?;
    let mut found = vec![];
    let mut text_end = None;
    let mut excluded = 0;
    for (event, range) in Parser::new(source).into_offset_iter() {
        match event {
            Event::Start(
                Tag::CodeBlock(_) | Tag::Link { .. } | Tag::Image { .. } | Tag::HtmlBlock,
            ) => {
                excluded += 1;
                text_end = None;
            }
            Event::End(TagEnd::CodeBlock | TagEnd::Link | TagEnd::Image | TagEnd::HtmlBlock) => {
                excluded -= 1;
                text_end = None;
            }
            Event::Text(_) if excluded == 0 => text_end = Some(range),
            Event::Code(id) if excluded == 0 => {
                if let Some(previous) = text_end.take() {
                    for (prefix, definition, lean) in [
                        ("{anchor}", true, false),
                        ("{anchor-ref}", false, false),
                        ("{lean.type}", false, true),
                    ] {
                        if previous.end != range.start
                            || !source[previous.clone()].ends_with(prefix)
                        {
                            continue;
                        }
                        let start = range.start - prefix.len();
                        if source[..start].ends_with('\\') {
                            continue;
                        }
                        // Double-backtick spans are literal demonstrations, not roles.
                        if source[range.clone()] != format!("`{id}`") {
                            continue;
                        }
                        ensure!(lean || id_pattern.is_match(&id), "invalid anchor ID `{id}`");
                        found.push(Role {
                            range: start..range.end,
                            id: id.into_string(),
                            definition,
                            lean,
                        });
                        break;
                    }
                }
            }
            _ => text_end = None,
        }
    }
    Ok(found)
}

struct DirectiveBlock {
    range: Range<usize>,
    info: String,
    body: String,
}

fn directive_blocks(source: &str) -> Vec<DirectiveBlock> {
    let mut found = vec![];
    let mut block = None;
    for (event, range) in Parser::new(source).into_offset_iter() {
        match event {
            Event::Start(Tag::CodeBlock(CodeBlockKind::Fenced(info)))
                if [
                    "{heap}",
                    "{grammar}",
                    "{judgment}",
                    "{rule}",
                    "{example}",
                    "{lean.type}",
                    "{lean.judgment}",
                    "{lean.rule}",
                ]
                .iter()
                .any(|name| info.starts_with(name)) =>
            {
                block = Some(DirectiveBlock {
                    range,
                    info: info.into_string(),
                    body: String::new(),
                });
            }
            Event::Text(text) => {
                if let Some(block) = &mut block {
                    block.body.push_str(&text);
                }
            }
            Event::End(TagEnd::CodeBlock) => {
                if let Some(mut block) = block.take() {
                    block.range.end = range.end;
                    found.push(block);
                }
            }
            _ => {}
        }
    }
    found
}

fn chapter_roles(source: &str) -> Result<Vec<Role>> {
    let mut found = roles(source)?;
    for block in directive_blocks(source) {
        if block.info.split_whitespace().next() == Some("{example}") {
            // Example bodies are Markdown, unlike the other directive bodies.
            ensure!(
                !directive_blocks(&block.body)
                    .iter()
                    .any(|nested| nested.info.starts_with("{example}")),
                "example directives cannot be nested"
            );
            found.extend(roles(&block.body)?);
        }
    }
    Ok(found)
}

fn walk(chapters: &Value, f: &mut impl FnMut(&Value) -> Result<()>) -> Result<()> {
    if let Some(items) = chapters.as_array() {
        for item in items {
            if let Some(chapter) = item.get("Chapter") {
                f(chapter)?;
                walk(&chapter["sub_items"], f)?;
            }
        }
    }
    Ok(())
}

fn relative_html(from: &str, to: &str) -> Result<String> {
    // mdBook chapter paths are relative to the source directory.
    let parts = |s: &str| -> Result<Vec<String>> {
        Path::new(s)
            .components()
            .map(|c| match c {
                std::path::Component::Normal(p) => Ok(p.to_string_lossy().into_owned()),
                _ => bail!("chapter path must be relative and normalized: {s}"),
            })
            .collect()
    };
    let mut from = parts(from)?;
    from.pop();
    let mut to = parts(to)?;
    let file = to.last_mut().context("empty chapter path")?;
    *file = Path::new(file)
        .with_extension("html")
        .to_string_lossy()
        .into_owned();
    let common = from.iter().zip(&to).take_while(|(a, b)| a == b).count();
    let path = std::iter::repeat_n("..".to_owned(), from.len() - common)
        .chain(to[common..].iter().cloned())
        .collect::<Vec<_>>()
        .join("/");
    Ok(path
        .replace('%', "%25")
        .replace(' ', "%20")
        .replace('#', "%23")
        .replace('?', "%3F"))
}

fn render(
    source: &str,
    path: &str,
    anchors: &BTreeMap<String, String>,
    lean_root: Option<&Path>,
    scope: &str,
) -> Result<String> {
    let mut edits = vec![];
    for role in roles(source)? {
        ensure!(
            !role.lean,
            "lean.type has been replaced: use ```{{grammar}} path:Name with authored LaTeX in the body"
        );
        let target = anchors
            .get(&role.id)
            .with_context(|| format!("unknown anchor `{}`", role.id))?;
        let fragment = format!("claim-{}", role.id);
        let href = if target == path {
            format!("#{fragment}")
        } else {
            format!("{}#{fragment}", relative_html(path, target)?)
        };
        let id_attr = if role.definition {
            format!(" id=\"{fragment}\"")
        } else {
            String::new()
        };
        let label = if role.definition { "spec" } else { "ref" };
        edits.push((role.range, format!(
            "<a{id_attr} class=\"spec-shield\" href=\"{}\" aria-label=\"{label}: {}\"><span class=\"spec-shield-label\">{label}</span><span class=\"spec-shield-name\">{}</span></a>",
            escape(&href), escape(&role.id), escape(&role.id))));
    }
    for (event, range) in Parser::new(source).into_offset_iter() {
        if matches!(event, Event::Start(Tag::Paragraph)) {
            ensure!(
                !source[range.clone()].starts_with("{example} "),
                "the paragraph {{example}} marker has been replaced: use a fenced ```{{example}} path:anchor with a Markdown body and a Lean test, or label an unfinished scenario as informational"
            );
            if source[range.clone()].starts_with("{informational} ") {
                edits.push((
                    range.start..range.start + "{informational}".len(),
                    "<span class=\"informational-label\">Informational</span>".to_owned(),
                ));
            }
        }
    }

    for block in directive_blocks(source) {
        let start = block.range.start;
        let kind = block.info;
        let facts = block.body;
        let (directive, argument) = kind.split_once(char::is_whitespace).unwrap_or((&kind, ""));
        ensure!(
            !["{heap}", "{grammar}", "{rule}", "{judgment}", "{example}"]
                .iter()
                .any(|name| directive.starts_with(name) && directive != *name),
            "separate the directive name and citation with whitespace"
        );
        ensure!(!matches!(directive, "{lean.type}" | "{lean.judgment}" | "{lean.rule}"),
                        "{directive} has been replaced: use ```{{grammar}} path:Name, ```{{judgment}} path:Name, or ```{{rule}} path:Name.case with authored LaTeX in the body");
        let id = format!("{scope}-{start}");
        if directive == "{example}" {
            ensure!(
                argument.split_whitespace().count() == 1,
                "example requires exactly one opening-line citation: ```{{example}} path:anchor"
            );
            ensure!(!facts.trim().is_empty(), "example requires a Markdown body");
            let root =
                lean_root.context("Lean directives require preprocessor.dada.lean-source")?;
            let lean_source = lean::example_source(root, argument.trim())?;
            let body = render(&facts, path, anchors, lean_root, &id)?;
            let group = escape(&format!("example-{id}"));
            // Blank lines terminate the raw HTML blocks so mdBook's
            // own Markdown renderer handles the authored body.
            edits.push((block.range, format!(
                            "\n<figure class=\"lean-declaration lean-group lean-example\"><div class=\"lean-selector\" role=\"group\" aria-label=\"Example view\"><span class=\"example-label\">Example</span><label><input type=\"radio\" name=\"{group}\" value=\"rendered\" checked> Rendered</label><label><input type=\"radio\" name=\"{group}\" value=\"lean\"> Lean</label></div><div class=\"lean-example-body\">\n\n{}\n\n</div><div class=\"lean-source\">{lean_source}</div></figure>\n\n",
                            body.trim_matches('\n')
                        )));
            continue;
        }
        let view = match directive {
            "{grammar}" => Some(lean::View::Grammar),
            "{judgment}" => Some(lean::View::Judgment),
            "{rule}" => Some(lean::View::Rule),
            _ => None,
        };
        if let Some(view) = view {
            let root =
                lean_root.context("Lean directives require preprocessor.dada.lean-source")?;
            edits.push((
                block.range,
                format!(
                    "\n{}\n",
                    lean::render_authored(root, argument.trim(), &facts, view, &id)?
                ),
            ));
            continue;
        }
        ensure!(
            argument.trim().is_empty(),
            "{directive} does not accept opening-line arguments"
        );
        let graph = graph::render(&facts)?;
        let group = escape(&format!("heap-{id}"));
        let source = escape(&facts).replace('\n', "&#10;");
        edits.push((block.range, format!("\n<figure class=\"heap-figure\"><div class=\"lean-selector\" role=\"group\" aria-label=\"Diagram view\"><label><input type=\"radio\" name=\"{group}\" value=\"rendered\" checked> Rendered</label><label><input type=\"radio\" name=\"{group}\" value=\"facts\"> Facts</label></div>{graph}<pre class=\"heap-facts\"><code>{source}</code></pre></figure>\n")));
    }
    edits.sort_by_key(|(range, _)| range.start);
    let mut result = String::new();
    let mut end = 0;
    for (range, replacement) in edits {
        ensure!(range.start >= end, "overlapping markup");
        result.push_str(&source[end..range.start]);
        result.push_str(&replacement);
        end = range.end;
    }
    result.push_str(&source[end..]);
    Ok(result)
}

pub fn process(book: &mut Value) -> Result<()> {
    process_with_lean(book, None)
}

pub fn process_with_lean(book: &mut Value, lean_root: Option<&Path>) -> Result<()> {
    let key = if book.get("items").is_some_and(Value::is_array) {
        "items"
    } else if book.get("sections").is_some_and(Value::is_array) {
        "sections"
    } else {
        bail!("unsupported mdBook input: expected an items or sections array");
    };
    let mut anchors = BTreeMap::new();
    walk(&book[key], &mut |chapter| {
        let source = chapter["content"]
            .as_str()
            .context("chapter has no content")?;
        let path = chapter["path"].as_str().context("chapter has no path")?;
        lint::check_latex(source, path)?;
        for role in chapter_roles(source).with_context(|| path.to_owned())? {
            if role.definition {
                if let Some(previous) = anchors.insert(role.id.clone(), path.to_owned()) {
                    bail!("duplicate anchor `{}` in {previous} and {path}", role.id);
                }
            }
        }
        Ok(())
    })?;
    fn update(
        items: &mut Value,
        anchors: &BTreeMap<String, String>,
        lean_root: Option<&Path>,
    ) -> Result<()> {
        if let Some(items) = items.as_array_mut() {
            for item in items {
                if let Some(chapter) = item.get_mut("Chapter") {
                    let path = chapter["path"].as_str().context("chapter has no path")?;
                    let source = chapter["content"]
                        .as_str()
                        .context("chapter has no content")?;
                    let content = render(source, path, anchors, lean_root, path)
                        .with_context(|| format!("chapter {path}"))?;
                    chapter["content"] = Value::String(content);
                    update(&mut chapter["sub_items"], anchors, lean_root)?;
                }
            }
        }
        Ok(())
    }
    update(&mut book[key], &anchors, lean_root)
}

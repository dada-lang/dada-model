//! Presentation-only mdBook processing. Associations are not verification evidence.
pub mod graph;
pub mod lean;
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
            for (marker, label, class) in [
                ("{informational}", "Informational", "informational-label"),
                ("{example}", "Example", "example-label"),
            ] {
                if source[range.clone()].starts_with(&format!("{marker} ")) {
                    edits.push((
                        range.start..range.start + marker.len(),
                        format!("<span class=\"{class}\">{label}</span>"),
                    ));
                }
            }
        }
    }

    let mut block = None;
    for (event, range) in Parser::new(source).into_offset_iter() {
        match event {
            Event::Start(Tag::CodeBlock(CodeBlockKind::Fenced(info)))
                if info.starts_with("{grammar}")
                    || info.starts_with("{rule}")
                    || info.starts_with("{judgment}")
                    || matches!(
                        info.split_whitespace().next(),
                        Some(
                            "{heap}"
                                | "{grammar}"
                                | "{lean.type}"
                                | "{lean.judgment}"
                                | "{lean.rule}"
                                | "{rule}"
                                | "{judgment}"
                        )
                    ) =>
            {
                block = Some((range.start, info.into_string(), String::new()));
            }
            Event::Text(text) => {
                if let Some((_, _, facts)) = &mut block {
                    facts.push_str(&text);
                }
            }
            Event::End(TagEnd::CodeBlock) => {
                if let Some((start, kind, facts)) = block.take() {
                    let (directive, argument) =
                        kind.split_once(char::is_whitespace).unwrap_or((&kind, ""));
                    ensure!(
                        !["{grammar}", "{rule}", "{judgment}"]
                            .iter()
                            .any(|name| directive.starts_with(name) && directive != *name),
                        "separate the directive name and citation with whitespace"
                    );
                    ensure!(!matches!(directive, "{lean.type}" | "{lean.judgment}" | "{lean.rule}"),
                        "{directive} has been replaced: use ```{{grammar}} path:Name, ```{{judgment}} path:Name, or ```{{rule}} path:Name.case with authored LaTeX in the body");
                    let view = match directive {
                        "{grammar}" => Some(lean::View::Grammar),
                        "{judgment}" => Some(lean::View::Judgment),
                        "{rule}" => Some(lean::View::Rule),
                        _ => None,
                    };
                    if let Some(view) = view {
                        let root = lean_root
                            .context("Lean directives require preprocessor.dada.lean-source")?;
                        let id = format!("{path}-{start}");
                        edits.push((
                            start..range.end,
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
                    let group = escape(&format!("heap-{path}-{start}"));
                    let source = escape(&facts).replace('\n', "&#10;");
                    edits.push((start..range.end, format!("\n<figure class=\"heap-figure\"><div class=\"lean-selector\" role=\"group\" aria-label=\"Diagram view\"><label><input type=\"radio\" name=\"{group}\" value=\"rendered\" checked> Rendered</label><label><input type=\"radio\" name=\"{group}\" value=\"facts\"> Facts</label></div>{graph}<pre class=\"heap-facts\"><code>{source}</code></pre></figure>\n")));
                }
            }
            _ => {}
        }
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
        for role in roles(source).with_context(|| path.to_owned())? {
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
                    let content = render(source, path, anchors, lean_root)
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

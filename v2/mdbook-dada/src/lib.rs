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

// Markdown otherwise consumes TeX row breaks and rewrites primes via smart
// punctuation. Protect explicit math before any roles or directives are parsed.
// The doubled delimiter backslashes are the book's Markdown authoring spelling;
// the HTML text passed to MathJax contains ordinary single-backslash delimiters.
fn protect_math(source: &str) -> String {
    let literal: Vec<_> = Parser::new(source)
        .into_offset_iter()
        .filter_map(|(event, range)| match event {
            Event::Start(
                Tag::CodeBlock(_) | Tag::HtmlBlock | Tag::Link { .. } | Tag::Image { .. },
            )
            | Event::Code(_)
            | Event::Html(_)
            | Event::InlineHtml(_) => Some(range),
            _ => None,
        })
        .collect();
    let mut output = String::new();
    let mut end = 0;
    for (start, _) in source.match_indices(r"\\") {
        if start < end
            || source[..start].ends_with('\\')
            || literal.iter().any(|range| range.contains(&start))
        {
            continue;
        }
        let (display, closing) = match source.as_bytes().get(start + 2) {
            Some(b'[') => (true, r"\\]"),
            Some(b'(') => (false, r"\\)"),
            _ => continue,
        };
        let body_start = start + 3;
        let Some(close) = source[body_start..].find(closing).map(|i| body_start + i) else {
            continue;
        };
        if literal.iter().any(|range| range.contains(&close)) {
            continue;
        }
        let body = &source[body_start..close];
        output.push_str(&source[end..start]);
        if display {
            let tex = escape(body).replace('\n', "&#10;");
            output.push_str(&format!(
                "\n\n<div class=\"math-display\">\\[{tex}\\]</div>\n\n"
            ));
        } else {
            // Inline HTML does not suppress Markdown parsing of its contents.
            // Entities keep every TeX punctuation character out of that parser.
            let tex: String = format!("\\({body}\\)")
                .chars()
                .map(|c| {
                    if c.is_alphanumeric() || c == ' ' {
                        c.to_string()
                    } else {
                        format!("&#{};", u32::from(c))
                    }
                })
                .collect();
            output.push_str(&format!("<span class=\"math-inline\">{tex}</span>"));
        }
        end = close + closing.len();
    }
    output.push_str(&source[end..]);
    output
}

#[derive(Debug)]
struct Role {
    range: Range<usize>,
    id: String,
    definition: bool,
    label: Option<&'static str>,
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
                    for (prefix, definition, label, lean) in [
                        ("{anchor}", true, None, false),
                        ("{definition}", true, Some("definition"), false),
                        ("{obligation}", true, Some("proof obligation"), false),
                        ("{anchor-ref}", false, None, false),
                        ("{lean.type}", false, None, true),
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
                            label,
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

#[derive(Clone, Copy)]
enum MarkdownDirective {
    Definition,
    Example,
    Theorem,
    Lemma,
}

impl MarkdownDirective {
    fn parse(name: &str) -> Option<Self> {
        match name {
            "{definition}" => Some(Self::Definition),
            "{example}" => Some(Self::Example),
            "{theorem}" => Some(Self::Theorem),
            "{lemma}" => Some(Self::Lemma),
            _ => None,
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Definition => "definition",
            Self::Example => "example",
            Self::Theorem => "theorem",
            Self::Lemma => "lemma",
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::Definition => "Definition",
            Self::Example => "Example",
            Self::Theorem => "Theorem",
            Self::Lemma => "Lemma",
        }
    }

    fn definition_label(self) -> &'static str {
        match self {
            Self::Definition => "definition",
            Self::Example => "anchor",
            Self::Theorem => "theorem",
            Self::Lemma => "lemma",
        }
    }
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
                    "{definition}",
                    "{theorem}",
                    "{lemma}",
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
    let protected = protect_math(source);
    let mut found = roles(&protected)?;
    for block in directive_blocks(&protected) {
        if block
            .info
            .split_whitespace()
            .next()
            .and_then(MarkdownDirective::parse)
            .is_some()
        {
            // These bodies are Markdown; grammar, judgment, and rule bodies are TeX.
            ensure!(
                !directive_blocks(&block.body).iter().any(|nested| {
                    ["{definition}", "{example}", "{theorem}", "{lemma}"]
                        .iter()
                        .any(|name| nested.info.starts_with(name))
                }),
                "definition, example, theorem, and lemma directives cannot be nested within one another"
            );
            found.extend(roles(&protect_math(&block.body))?);
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

fn render_role(
    role: &Role,
    path: &str,
    anchors: &BTreeMap<String, String>,
    definition_label: &str,
) -> Result<String> {
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
    let label = if role.definition {
        role.label.unwrap_or(definition_label)
    } else {
        "ref"
    };
    Ok(format!(
        "<a{id_attr} class=\"spec-shield\" href=\"{}\" aria-label=\"{label}: {}\"><span class=\"spec-shield-label\">{label}</span><span class=\"spec-shield-name\">{}</span></a>",
        escape(&href), escape(&role.id), escape(&role.id)
    ))
}

// Only a sequence of declaration roles at the very start belongs in the header.
// Roles later in prose, inside literals, or inside nested directives stay put.
fn markdown_heading<'a>(
    source: &'a str,
    path: &str,
    anchors: &BTreeMap<String, String>,
    definition_label: &str,
) -> Result<(String, &'a str)> {
    let protected = protect_math(source);
    let mut heading = Vec::new();
    let mut end = 0;
    for role in roles(&protected)? {
        if !protected[end..role.range.start].trim().is_empty()
            || !role.definition
            || role.label == Some("proof obligation")
        {
            break;
        }
        heading.push(render_role(&role, path, anchors, definition_label)?);
        // A promoted role is preceded only by whitespace and other roles, so
        // math protection has not changed its source offsets.
        end = role.range.end;
    }
    Ok((heading.join(" "), &source[end..]))
}

/// Shared header for every rendered/source pair. The heading is generated HTML;
/// labels, group names, and radio values are escaped here.
pub(crate) fn selector_header(
    label: &str,
    heading: Option<&str>,
    group: &str,
    rendered_value: &str,
    alternate: &str,
) -> String {
    let label = escape(label);
    let fallback = format!("<span class=\"block-label\">{label}</span>");
    let heading = heading.unwrap_or(&fallback);
    let group = escape(group);
    let rendered_value = escape(rendered_value);
    let alternate_value = escape(&alternate.to_ascii_lowercase());
    let alternate = escape(alternate);
    format!("<div class=\"lean-selector\" role=\"group\" aria-label=\"{label} view\"><div class=\"block-heading\">{heading}</div><div class=\"view-options\"><label><input type=\"radio\" name=\"{group}\" value=\"{rendered_value}\" checked> Rendered</label><label><input type=\"radio\" name=\"{group}\" value=\"{alternate_value}\"> {alternate}</label></div></div>")
}

fn render(
    source: &str,
    path: &str,
    anchors: &BTreeMap<String, String>,
    lean_root: Option<&Path>,
    scope: &str,
    definition_label: &str,
) -> Result<String> {
    let protected = protect_math(source);
    let source = protected.as_str();
    let mut edits = vec![];
    for role in roles(source)? {
        let rendered = render_role(&role, path, anchors, definition_label)?;
        edits.push((role.range, rendered));
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
            ![
                "{heap}",
                "{grammar}",
                "{rule}",
                "{judgment}",
                "{definition}",
                "{theorem}",
                "{lemma}",
                "{example}"
            ]
            .iter()
            .any(|name| directive.starts_with(name) && directive != *name),
            "separate the directive name and citation with whitespace"
        );
        ensure!(!matches!(directive, "{lean.type}" | "{lean.judgment}" | "{lean.rule}"),
                        "{directive} has been replaced: use ```{{grammar}} path:Name, ```{{judgment}} path:Name, or ```{{rule}} path:Name.case with authored LaTeX in the body");
        let id = format!("{scope}-{start}");
        if let Some(markdown) = MarkdownDirective::parse(directive) {
            let name = markdown.name();
            let label = markdown.label();
            let citations = argument.split_whitespace().count();
            if matches!(markdown, MarkdownDirective::Definition) {
                ensure!(
                    citations > 0,
                    "definition requires at least one opening-line citation"
                );
            } else {
                ensure!(
                    citations == 1,
                    "{name} requires exactly one opening-line citation"
                );
            }
            ensure!(!facts.trim().is_empty(), "{name} requires a Markdown body");
            let root =
                lean_root.context("Lean directives require preprocessor.dada.lean-source")?;
            let lean_source = match markdown {
                MarkdownDirective::Definition => lean::definition_source(root, argument)?,
                MarkdownDirective::Example => lean::example_source(root, argument.trim())?,
                MarkdownDirective::Theorem | MarkdownDirective::Lemma => {
                    lean::theorem_source(root, argument.trim())?
                }
            };
            let heading_label = if matches!(markdown, MarkdownDirective::Example) {
                "example"
            } else {
                markdown.definition_label()
            };
            let (heading, body) = markdown_heading(&facts, path, anchors, heading_label)?;
            ensure!(
                !body.trim().is_empty(),
                "{name} requires a Markdown body after its heading anchors"
            );
            let body = render(
                body,
                path,
                anchors,
                lean_root,
                &id,
                markdown.definition_label(),
            )?;
            let selector = selector_header(
                label,
                (!heading.is_empty()).then_some(heading.as_str()),
                &format!("{name}-{id}"),
                "rendered",
                "Lean",
            );
            // Blank lines terminate raw HTML blocks so mdBook renders the body
            // as Markdown, including its explicit math delimiters and proof prose.
            edits.push((block.range, format!(
                "\n<figure class=\"lean-declaration lean-group lean-markdown lean-{name}\">{selector}<div class=\"lean-markdown-body\">\n\n{}\n\n</div><div class=\"lean-source\">{lean_source}</div></figure>\n\n",
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
        let selector = selector_header("Diagram", None, &format!("heap-{id}"), "rendered", "Facts");
        let source = escape(&facts).replace('\n', "&#10;");
        edits.push((block.range, format!("\n<figure class=\"heap-figure\">{selector}{graph}<pre class=\"heap-facts\"><code>{source}</code></pre></figure>\n")));
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
                    let content = render(source, path, anchors, lean_root, path, "anchor")
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

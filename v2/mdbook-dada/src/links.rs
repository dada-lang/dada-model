//! Deterministic inventory of authored links and their reading order.
//!
//! This module does not guess which words denote concepts. Reviewers classify
//! the extracted links and inspect unlinked prose/math for omissions. A local
//! link only identifies its unit; it does not establish that the linked subject
//! has already been introduced within that unit.
use crate::{
    inventory::{self, Input, Inventory},
    units::UnitKind,
};
use anyhow::{bail, ensure, Context, Result};
use pulldown_cmark::{BrokenLink, Event, LinkType, Options, Parser, Tag, TagEnd};
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, BTreeSet},
    ops::Range,
    path::Path,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Location {
    pub path: String,
    pub range: Range<usize>,
    pub line: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Chapter {
    pub path: String,
    pub order: usize,
    pub summary_location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TargetKind {
    Unit,
    Heading,
    LegacyAnchor,
    Chapter,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Target {
    /// Canonical repository-relative chapter path followed by its actual HTML fragment.
    pub key: String,
    /// The reviewable definition scope, rather than just its heading or marker.
    pub location: Location,
    /// Exact authored construct corresponding to the rendered link landing point.
    pub anchor_location: Location,
    pub kind: TargetKind,
    pub unit_id: Option<String>,
    pub chapter_order: Option<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum LinkTarget {
    Internal { target: Target },
    External { url: String },
    Asset { path: String },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Direction {
    Backward,
    Local,
    Forward,
    Unordered,
    External,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LinkSyntax {
    Markdown,
    AnchorRef,
    MathJax,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LinkOccurrence {
    /// Stable for an unchanged authored unit: unit ID and occurrence ordinal.
    pub id: String,
    pub source: Location,
    pub destination: String,
    pub label: String,
    pub syntax: LinkSyntax,
    pub target: LinkTarget,
    pub direction: Direction,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceLinks {
    pub unit_id: String,
    pub unit_kind: UnitKind,
    pub audit_required: bool,
    pub location: Location,
    pub occurrences: Vec<LinkOccurrence>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LinkInventory {
    pub sources: BTreeMap<String, SourceLinks>,
    pub chapters: Vec<Chapter>,
    pub targets: BTreeMap<String, Target>,
    /// Strongly connected groups in the unclassified unit-link graph. Navigation
    /// links may account for a cycle; evidence must say which edges are conceptual.
    pub cycles: Vec<Vec<String>>,
    pub summary_path: String,
}

/// Namespace for the inventory builder; retained separately from its serializable result.
pub struct Links;
impl Links {
    pub fn build(inventory: &Inventory) -> Result<LinkInventory> {
        LinkInventory::build(inventory)
    }
}

#[derive(Debug)]
struct RawLink {
    range: Range<usize>,
    destination: String,
    label: String,
    syntax: LinkSyntax,
}

fn location(path: &str, source: &str, range: Range<usize>) -> Location {
    Location {
        path: path.to_owned(),
        line: source[..range.start]
            .bytes()
            .filter(|b| *b == b'\n')
            .count()
            + 1,
        range,
    }
}

fn blank(bytes: &mut [u8], range: Range<usize>) {
    for byte in &mut bytes[range] {
        if !matches!(*byte, b'\n' | b'\r') {
            *byte = b' ';
        }
    }
}

/// Remove presentation fences without moving byte offsets. This makes reference
/// definitions and Markdown in directive bodies part of the same source document.
fn flatten(
    source: &str,
    offset: usize,
    bytes: &mut [u8],
    math: &mut Vec<Range<usize>>,
) -> Result<()> {
    for block in crate::directive_blocks(source) {
        let raw = &source[block.range.clone()];
        let start = raw.find('\n').context("directive has no body")? + 1;
        let end = raw
            .trim_end_matches(['\n', '\r'])
            .rfind('\n')
            .context("directive has no closing fence")?
            + 1;
        let directive = block.info.split_whitespace().next().unwrap_or("");
        let mut body_start = start;
        for line in raw[start..end].split_inclusive('\n') {
            if !line.starts_with(':') {
                break;
            }
            body_start += line.len();
        }
        let base = offset + block.range.start;
        if directive == "{heap}" {
            blank(bytes, base..offset + block.range.end);
            continue;
        }
        blank(bytes, base..base + body_start);
        blank(bytes, base + end..offset + block.range.end);
        let body_range = base + body_start..base + end;
        if matches!(directive, "{grammar}" | "{judgment}" | "{rule}") {
            math.push(body_range);
        } else {
            flatten(&raw[body_start..end], base + body_start, bytes, math)?;
        }
    }
    Ok(())
}

fn literal_ranges(source: &str) -> Vec<Range<usize>> {
    Parser::new(source)
        .into_offset_iter()
        .filter_map(|(event, range)| match event {
            Event::Start(Tag::CodeBlock(_) | Tag::HtmlBlock)
            | Event::Code(_)
            | Event::Html(_)
            | Event::InlineHtml(_) => Some(range),
            _ => None,
        })
        .collect()
}

fn inside(ranges: &[Range<usize>], offset: usize) -> bool {
    ranges.iter().any(|r| r.contains(&offset))
}

fn escaped(source: &str, offset: usize) -> bool {
    source[..offset]
        .bytes()
        .rev()
        .take_while(|b| *b == b'\\')
        .count()
        % 2
        == 1
}

fn explicit_math(source: &str, existing: &[Range<usize>]) -> Result<Vec<Range<usize>>> {
    let literals = literal_ranges(source);
    let mut found = Vec::new();
    let mut previous_end = 0;
    for (start, _) in source.match_indices(r"\\") {
        if start < previous_end
            || escaped(source, start)
            || inside(&literals, start)
            || inside(existing, start)
        {
            continue;
        }
        let closing = match source.as_bytes().get(start + 2) {
            Some(b'[') => r"\\]",
            Some(b'(') => r"\\)",
            _ => continue,
        };
        let end = source[start + 3..]
            .find(closing)
            .map(|n| start + 3 + n + closing.len())
            .context("unclosed explicit mathematics")?;
        found.push(start..end);
        previous_end = end;
    }
    Ok(found)
}

fn group(source: &str, start: usize) -> Result<(Range<usize>, usize)> {
    ensure!(
        source.as_bytes().get(start) == Some(&b'{'),
        "expected braced MathJax href argument"
    );
    let mut depth = 1;
    for (offset, ch) in source[start + 1..].char_indices() {
        let index = start + 1 + offset;
        if escaped(source, index) {
            continue;
        }
        if ch == '{' {
            depth += 1;
        }
        if ch == '}' {
            depth -= 1;
            if depth == 0 {
                return Ok((start + 1..index, index + 1));
            }
        }
    }
    bail!("unclosed MathJax href argument")
}

fn math_links(source: &str, region: Range<usize>) -> Result<Vec<RawLink>> {
    let mut found = Vec::new();
    for (relative, _) in source[region.clone()].match_indices(r"\href") {
        let start = region.start + relative;
        if escaped(source, start)
            || source
                .as_bytes()
                .get(start + 5)
                .is_some_and(u8::is_ascii_alphabetic)
        {
            continue;
        }
        let line_start = source[..start].rfind('\n').map_or(region.start, |n| n + 1);
        if source[line_start..start]
            .match_indices('%')
            .any(|(i, _)| !escaped(source, line_start + i))
        {
            continue;
        }
        let argument = start + 5 + source[start + 5..region.end].len()
            - source[start + 5..region.end].trim_start().len();
        let (url, after_url) = group(&source[..region.end], argument)?;
        let second = after_url + source[after_url..region.end].len()
            - source[after_url..region.end].trim_start().len();
        let (label, end) = group(&source[..region.end], second)?;
        ensure!(
            end <= region.end,
            "MathJax href escapes its mathematics block"
        );
        let destination = &source[url];
        ensure!(!destination.contains(['\\', '{', '}']), "computed or escaped MathJax href destinations are unsupported; use a literal URL with percent escapes");
        found.push(RawLink {
            range: start..end,
            destination: destination.to_owned(),
            label: source[label].to_owned(),
            syntax: LinkSyntax::MathJax,
        });
    }
    Ok(found)
}

struct Document {
    markdown: String,
    links: Vec<RawLink>,
}
fn document(source: &str, path: &str) -> Result<Document> {
    let mut bytes = source.as_bytes().to_vec();
    let mut math = Vec::new();
    flatten(source, 0, &mut bytes, &mut math).with_context(|| format!("{path}:1"))?;
    let flat = String::from_utf8(bytes.clone())?;
    math.extend(explicit_math(&flat, &math).with_context(|| format!("{path}:1"))?);
    let mut links = Vec::new();
    for region in math {
        links.extend(
            math_links(source, region.clone()).with_context(|| {
                format!("{path}:{}", location(path, source, region.clone()).line)
            })?,
        );
        blank(&mut bytes, region);
    }
    let markdown = String::from_utf8(bytes)?;
    let mut current_link = None;
    let mut unresolved = Vec::new();
    let mut callback = |broken: BrokenLink<'_>| {
        if matches!(broken.link_type, LinkType::Reference | LinkType::Collapsed) {
            unresolved.push(broken.span);
        }
        None
    };
    for (event, range) in Parser::new_with_broken_link_callback(
        &markdown,
        Options::ENABLE_HEADING_ATTRIBUTES,
        Some(&mut callback),
    )
    .into_offset_iter()
    {
        match event {
            Event::Start(Tag::Link { dest_url, .. }) => {
                current_link = Some(RawLink {
                    range,
                    destination: dest_url.into_string(),
                    label: String::new(),
                    syntax: LinkSyntax::Markdown,
                });
            }
            Event::Text(text) | Event::Code(text) if current_link.is_some() => {
                current_link.as_mut().unwrap().label.push_str(&text);
            }
            Event::End(TagEnd::Link) => {
                if let Some(link) = current_link.take() {
                    links.push(link);
                }
            }
            Event::Html(html) | Event::InlineHtml(html) => {
                // HTML comments are deliberately inert. An actual HTML link must
                // not disappear from coverage merely because it is not Markdown.
                let text = html.trim_start();
                ensure!(
                    text.starts_with("<!--") || !text.to_ascii_lowercase().contains("href"),
                    "{path}:{}: HTML links are not supported by link auditing; use a Markdown link",
                    location(path, source, range).line
                );
            }
            _ => {}
        }
    }
    if let Some(range) = unresolved.first() {
        bail!(
            "{path}:{}: unresolved reference-style link; supply its Markdown link definition",
            location(path, source, range.clone()).line
        );
    }
    for role in crate::roles(&markdown)? {
        if !role.definition && !role.lean {
            links.push(RawLink {
                range: role.range,
                destination: role.id.clone(),
                label: role.id,
                syntax: LinkSyntax::AnchorRef,
            });
        }
    }
    links.sort_by_key(|link| (link.range.start, link.range.end));
    Ok(Document { markdown, links })
}

fn decode_url(part: &str) -> Result<String> {
    let mut decoded = Vec::new();
    let bytes = part.as_bytes();
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] == b'%' {
            ensure!(index + 2 < bytes.len(), "incomplete URL percent escape");
            let hex = std::str::from_utf8(&bytes[index + 1..index + 3])?;
            decoded.push(u8::from_str_radix(hex, 16).context("invalid URL percent escape")?);
            index += 3;
        } else {
            decoded.push(bytes[index]);
            index += 1;
        }
    }
    let decoded = String::from_utf8(decoded)?;
    ensure!(
        !decoded.contains(['\\', '\0']) && !decoded.chars().any(char::is_control),
        "unsupported URL path or fragment"
    );
    Ok(decoded)
}

fn external(destination: &str) -> Result<bool> {
    if destination.starts_with("//") {
        return Ok(true);
    }
    if let Some((scheme, _)) = destination.split_once(':') {
        if !scheme.contains('/') && !scheme.contains('#') {
            ensure!(
                matches!(
                    scheme.to_ascii_lowercase().as_str(),
                    "http" | "https" | "mailto"
                ),
                "unsupported link URL scheme `{scheme}`"
            );
            return Ok(true);
        }
    }
    Ok(false)
}

fn relative_target(from: &str, destination: &str, markdown_root: &str) -> Result<String> {
    ensure!(
        !destination.starts_with('/'),
        "root-relative links are ambiguous; use a chapter-relative URL"
    );
    let mut parts: Vec<_> = from.split('/').collect();
    parts.pop();
    for part in destination.split('/') {
        match part {
            "" | "." => {}
            ".." => {
                ensure!(
                    parts.len() > markdown_root.split('/').count(),
                    "link escapes the book source root"
                );
                parts.pop();
            }
            _ => parts.push(part),
        }
    }
    let path = parts.join("/");
    ensure!(
        Path::new(&path).starts_with(markdown_root),
        "link escapes the book source root"
    );
    Ok(path)
}

fn chapter_path(from: &str, destination: &str, markdown_root: &str) -> Result<String> {
    let destination = decode_url(destination)?;
    let mut path = relative_target(from, &destination, markdown_root)?;
    if path.ends_with(".html") {
        path.truncate(path.len() - 5);
        path.push_str(".md");
    }
    Ok(path)
}

fn insert_target(targets: &mut BTreeMap<String, Target>, target: Target) -> Result<()> {
    ensure!(
        !targets.contains_key(&target.key),
        "{}:{}: ambiguous duplicate link target `{}`",
        target.location.path,
        target.location.line,
        target.key
    );
    targets.insert(target.key.clone(), target);
    Ok(())
}

fn slug(text: &str) -> String {
    // Match mdbook-html 0.5.4, utils::id_from_content.
    text.trim()
        .to_lowercase()
        .chars()
        .filter_map(|c| {
            if c.is_alphanumeric() || c == '_' || c == '-' {
                Some(c)
            } else if c.is_whitespace() {
                Some('-')
            } else {
                None
            }
        })
        .collect()
}

impl LinkInventory {
    pub fn build(inventory: &Inventory) -> Result<Self> {
        let markdown_root = inventory::relative_path(
            &inventory.root,
            &inventory
                .source_configuration
                .markdown_root(&inventory.root)?,
        )?;
        let summary_path = format!("{markdown_root}/SUMMARY.md");
        let summary = inventory
            .sources
            .get(&summary_path)
            .context("link order requires the configured book's SUMMARY.md")?;
        let mut chapters = Vec::new();
        let mut chapter_orders = BTreeMap::new();
        for (event, range) in Parser::new(summary).into_offset_iter() {
            if let Event::Start(Tag::Link { dest_url, .. }) = event {
                ensure!(
                    !external(&dest_url)?,
                    "{summary_path}:{}: external SUMMARY entries have no source order",
                    location(&summary_path, summary, range.clone()).line
                );
                ensure!(
                    !dest_url.contains(['#', '?']),
                    "{summary_path}: SUMMARY chapters cannot contain fragments or queries"
                );
                let path = chapter_path(&summary_path, &dest_url, &markdown_root)?;
                ensure!(
                    inventory.sources.contains_key(&path),
                    "{summary_path}: SUMMARY references missing chapter `{path}`"
                );
                ensure!(
                    !chapter_orders.contains_key(&path),
                    "{summary_path}: duplicate chapter `{path}` makes reading order ambiguous"
                );
                let order = chapters.len();
                chapter_orders.insert(path.clone(), order);
                chapters.push(Chapter {
                    path,
                    order,
                    summary_location: location(&summary_path, summary, range),
                });
            }
        }
        let mut targets = BTreeMap::new();
        let mut global_anchors = BTreeMap::new();
        let mut documents = BTreeMap::new();
        for (path, source) in &inventory.sources {
            let doc = document(source, path)?;
            let chapter_order = chapter_orders.get(path).copied();
            insert_target(
                &mut targets,
                Target {
                    key: path.clone(),
                    location: location(path, source, 0..source.len()),
                    anchor_location: location(path, source, 0..0),
                    kind: TargetKind::Chapter,
                    unit_id: None,
                    chapter_order,
                },
            )?;
            for unit in inventory
                .units
                .values()
                .filter(|unit| &unit.source_path == path)
            {
                let key = format!("{path}#claim-{}", unit.id);
                ensure!(
                    global_anchors
                        .insert(unit.id.clone(), key.clone())
                        .is_none(),
                    "{path}:{}: duplicate anchor `{}`",
                    location(path, source, unit.range.clone()).line,
                    unit.id
                );
                // The generated anchor is on the unit header, not at the actual
                // defining sentence. Target review must inspect the complete unit.
                insert_target(
                    &mut targets,
                    Target {
                        key,
                        location: location(path, source, unit.range.clone()),
                        anchor_location: location(
                            path,
                            source,
                            unit.range.start
                                ..unit.range.start
                                    + unit.raw.find('\n').map_or(unit.raw.len(), |end| end + 1),
                        ),
                        kind: TargetKind::Unit,
                        unit_id: Some(unit.id.clone()),
                        chapter_order,
                    },
                )?;
            }
            for role in crate::roles(&doc.markdown)? {
                if role.definition {
                    let key = format!("{path}#claim-{}", role.id);
                    ensure!(
                        global_anchors
                            .insert(role.id.clone(), key.clone())
                            .is_none(),
                        "{path}:{}: duplicate anchor `{}`",
                        location(path, source, role.range.clone()).line,
                        role.id
                    );
                    let unit_id = inventory
                        .units
                        .values()
                        .find(|unit| {
                            unit.source_path == *path && unit.range.contains(&role.range.start)
                        })
                        .map(|unit| unit.id.clone());
                    insert_target(
                        &mut targets,
                        Target {
                            key,
                            location: location(path, source, role.range.clone()),
                            anchor_location: location(path, source, role.range),
                            kind: TargetKind::LegacyAnchor,
                            unit_id,
                            chapter_order,
                        },
                    )?;
                }
            }
            let mut heading = None;
            let mut used = BTreeSet::new();
            let mut headings = Vec::new();
            for (event, range) in Parser::new_ext(&doc.markdown, Options::ENABLE_HEADING_ATTRIBUTES)
                .into_offset_iter()
            {
                match event {
                    Event::Start(Tag::Heading { id, level, .. }) => {
                        heading = Some((range, level, id.map(|id| id.into_string()), String::new()))
                    }
                    Event::Text(text) | Event::Code(text) if heading.is_some() => {
                        heading.as_mut().unwrap().3.push_str(&text)
                    }
                    Event::End(TagEnd::Heading(_)) => {
                        if let Some((range, level, explicit, text)) = heading.take() {
                            let base = explicit.unwrap_or_else(|| slug(&text));
                            let mut id = base.clone();
                            let mut suffix = 0;
                            while !used.insert(id.clone()) {
                                suffix += 1;
                                id = format!("{base}-{suffix}");
                            }
                            headings.push((range, level, id));
                        }
                    }
                    _ => {}
                }
            }
            for (index, (range, level, id)) in headings.iter().enumerate() {
                let unit = inventory
                    .units
                    .values()
                    .find(|unit| unit.source_path == *path && unit.range.contains(&range.start));
                let end = headings[index + 1..]
                    .iter()
                    .find(|(_, next_level, _)| next_level <= level)
                    .map_or(source.len(), |(next, _, _)| next.start)
                    .min(unit.map_or(source.len(), |unit| unit.range.end));
                insert_target(
                    &mut targets,
                    Target {
                        key: format!("{path}#{id}"),
                        location: location(path, source, range.start..end),
                        anchor_location: location(path, source, range.clone()),
                        kind: TargetKind::Heading,
                        unit_id: unit.map(|unit| unit.id.clone()),
                        chapter_order,
                    },
                )?;
            }
            let boundaries: Vec<_> = targets
                .values()
                .filter(|target| {
                    target.location.path == *path && target.kind != TargetKind::Chapter
                })
                .map(|target| target.anchor_location.range.start)
                .collect();
            for target in targets.values_mut().filter(|target| {
                target.location.path == *path && target.kind == TargetKind::LegacyAnchor
            }) {
                let end = if let Some(unit) = target
                    .unit_id
                    .as_ref()
                    .and_then(|id| inventory.units.get(id))
                {
                    unit.range.end
                } else {
                    boundaries
                        .iter()
                        .copied()
                        .filter(|start| *start > target.location.range.start)
                        .min()
                        .unwrap_or(source.len())
                };
                target.location.range.end = end;
            }
            documents.insert(path.clone(), doc);
        }
        let mut sources = BTreeMap::new();
        for unit in inventory.units.values() {
            let source = &inventory.sources[&unit.source_path];
            let mut occurrences = Vec::new();
            for raw in documents[&unit.source_path]
                .links
                .iter()
                .filter(|link| unit.range.contains(&link.range.start))
            {
                let source_location = location(&unit.source_path, source, raw.range.clone());
                let target = resolve(
                    raw,
                    &unit.source_path,
                    &markdown_root,
                    inventory,
                    &targets,
                    &global_anchors,
                )
                .with_context(|| {
                    format!(
                        "{}:{}: link `{}`",
                        source_location.path, source_location.line, raw.destination
                    )
                })?;
                if let LinkTarget::Internal { target } = &target {
                    ensure!(
                        !chapter_orders.contains_key(&unit.source_path) || target.chapter_order.is_some(),
                        "{}:{}: published chapter links to unpublished target `{}`; add the target chapter to SUMMARY.md so its .html page exists",
                        source_location.path, source_location.line, target.key
                    );
                }
                let direction = match &target {
                    LinkTarget::Internal { target }
                        if target.unit_id.as_deref() == Some(&unit.id)
                            || (target.location.path == unit.source_path
                                && target.location.range.contains(&raw.range.start)) =>
                    {
                        Direction::Local
                    }
                    LinkTarget::Internal { target } if target.location.path == unit.source_path => {
                        if target.location.range.start < raw.range.start {
                            Direction::Backward
                        } else {
                            Direction::Forward
                        }
                    }
                    LinkTarget::Internal { target } => {
                        match (chapter_orders.get(&unit.source_path), target.chapter_order) {
                            (Some(from), Some(to)) if *from < to => Direction::Forward,
                            (Some(_), Some(_)) => Direction::Backward,
                            _ => Direction::Unordered,
                        }
                    }
                    _ => Direction::External,
                };
                occurrences.push(LinkOccurrence {
                    id: format!("{}:{}", unit.id, occurrences.len() + 1),
                    source: source_location,
                    destination: raw.destination.clone(),
                    label: raw.label.clone(),
                    syntax: raw.syntax,
                    target,
                    direction,
                });
            }
            sources.insert(
                unit.id.clone(),
                SourceLinks {
                    unit_id: unit.id.clone(),
                    unit_kind: unit.kind,
                    audit_required: true,
                    location: location(&unit.source_path, source, unit.range.clone()),
                    occurrences,
                },
            );
        }
        let cycles = cycles(&sources);
        Ok(Self {
            sources,
            chapters,
            targets,
            cycles,
            summary_path,
        })
    }

    pub fn occurrence(&self, id: &str) -> Option<&LinkOccurrence> {
        self.sources
            .values()
            .flat_map(|source| &source.occurrences)
            .find(|link| link.id == id)
    }

    /// A filesystem-safe, deterministic subject token for target audit records.
    pub fn target_subject(key: &str) -> String {
        inventory::hash(key.as_bytes())
    }

    /// Conservative snapshots: changes to chapter content, anchors, reference
    /// definitions, or SUMMARY ordering invalidate dependent audit evidence.
    pub fn inputs(&self, inventory: &Inventory) -> Vec<Input> {
        inventory
            .sources
            .iter()
            .map(|(path, content)| {
                Input::new(
                    format!("link-source:{path}"),
                    path.clone(),
                    1,
                    content.clone(),
                )
            })
            .collect()
    }
}

fn resolve(
    raw: &RawLink,
    from: &str,
    markdown_root: &str,
    inventory: &Inventory,
    targets: &BTreeMap<String, Target>,
    anchors: &BTreeMap<String, String>,
) -> Result<LinkTarget> {
    if raw.syntax == LinkSyntax::AnchorRef {
        let key = anchors
            .get(&raw.destination)
            .with_context(|| format!("unknown anchor `{}`", raw.destination))?;
        return Ok(LinkTarget::Internal {
            target: targets[key].clone(),
        });
    }
    if external(&raw.destination)? {
        return Ok(LinkTarget::External {
            url: raw.destination.clone(),
        });
    }
    let (path, fragment) = raw
        .destination
        .split_once('#')
        .map_or((raw.destination.as_str(), None), |(p, f)| (p, Some(f)));
    ensure!(
        !path.contains('?'),
        "query-bearing local links are unsupported; use a direct definition URL"
    );
    ensure!(raw.syntax != LinkSyntax::MathJax || !decode_url(path)?.ends_with(".md"), "MathJax links must use the rendered .html chapter URL; mdBook does not rewrite a raw \\href destination ending in .md");
    let path = if path.is_empty() {
        from.to_owned()
    } else {
        chapter_path(from, path, markdown_root)?
    };
    if !inventory.sources.contains_key(&path) {
        ensure!(
            fragment.is_none() && !path.ends_with(".md"),
            "unknown target chapter `{path}`"
        );
        ensure!(
            inventory::input_path(&inventory.root, &path)?.is_file(),
            "local link target must be a file, not a directory: {path}"
        );
        return Ok(LinkTarget::Asset { path });
    }
    let key = match fragment {
        Some(fragment) if !fragment.is_empty() => format!("{path}#{}", decode_url(fragment)?),
        _ => path,
    };
    let target = targets.get(&key).with_context(|| {
        format!("unknown target `{key}`; the path and anchor must identify the same chapter")
    })?;
    Ok(LinkTarget::Internal {
        target: target.clone(),
    })
}

fn cycles(sources: &BTreeMap<String, SourceLinks>) -> Vec<Vec<String>> {
    let graph: BTreeMap<_, BTreeSet<_>> = sources
        .iter()
        .map(|(id, source)| {
            (
                id.clone(),
                source
                    .occurrences
                    .iter()
                    .filter_map(|link| match &link.target {
                        LinkTarget::Internal { target } => target
                            .unit_id
                            .clone()
                            .filter(|other| other != id && sources.contains_key(other)),
                        _ => None,
                    })
                    .collect(),
            )
        })
        .collect();
    fn reachable(graph: &BTreeMap<String, BTreeSet<String>>, from: &str, to: &str) -> bool {
        let mut pending = vec![from.to_owned()];
        let mut seen = BTreeSet::new();
        while let Some(node) = pending.pop() {
            if node == to {
                return true;
            }
            if seen.insert(node.clone()) {
                pending.extend(graph[&node].iter().cloned());
            }
        }
        false
    }
    let mut remaining: BTreeSet<_> = graph.keys().cloned().collect();
    let mut result = Vec::new();
    while let Some(first) = remaining.pop_first() {
        let members: Vec<_> = remaining
            .iter()
            .filter(|other| reachable(&graph, &first, other) && reachable(&graph, other, &first))
            .cloned()
            .collect();
        if !members.is_empty() {
            let mut group = vec![first];
            for member in members {
                remaining.remove(&member);
                group.push(member);
            }
            result.push(group);
        }
    }
    result
}

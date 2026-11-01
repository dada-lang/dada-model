//! Named authored units, selected from the original Markdown before rendering.
//!
//! Byte ranges and `raw` preserve exactly what a reviewer was asked to compare.
//! The parser checks structure only; a citation does not establish correspondence.
use anyhow::{bail, ensure, Context, Result};
use pulldown_cmark::{CodeBlockKind, Event, Parser, Tag, TagEnd};
use serde::{Deserialize, Serialize};
use std::{collections::BTreeSet, ops::Range};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum UnitKind {
    Definition,
    Grammar,
    Judgment,
    Rule,
    Theorem,
    Lemma,
    Example,
}

impl UnitKind {
    pub fn parse(directive: &str) -> Option<Self> {
        Some(match directive {
            "{definition}" => Self::Definition,
            "{grammar}" => Self::Grammar,
            "{judgment}" => Self::Judgment,
            "{rule}" => Self::Rule,
            "{theorem}" => Self::Theorem,
            "{lemma}" => Self::Lemma,
            "{example}" => Self::Example,
            _ => return None,
        })
    }

    pub fn label(self) -> &'static str {
        match self {
            Self::Definition => "Definition",
            Self::Grammar => "Grammar",
            Self::Judgment => "Judgment",
            Self::Rule => "Rule",
            Self::Theorem => "Theorem",
            Self::Lemma => "Lemma",
            Self::Example => "Example",
        }
    }

    pub fn is_math(self) -> bool {
        matches!(self, Self::Grammar | Self::Judgment | Self::Rule)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SpecUnit {
    pub id: String,
    pub kind: UnitKind,
    /// Editorial stage, independent of the semantic kind. A draft may lack a
    /// formalization, but must never count as completed correspondence evidence.
    #[serde(default)]
    pub draft: bool,
    pub source_path: String,
    pub range: Range<usize>,
    pub body: String,
    pub raw: String,
    pub lean: Vec<String>,
    pub rust: Vec<String>,
    pub tests: Vec<String>,
    pub uses: Vec<String>,
}

fn valid_id(id: &str) -> bool {
    id.as_bytes().first().is_some_and(u8::is_ascii_alphanumeric)
        && id
            .bytes()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, b'.' | b'_' | b'-'))
}

fn parse_block(
    source: &str,
    path: &str,
    range: Range<usize>,
    info: &str,
) -> Result<Option<SpecUnit>> {
    let (directive, argument) = info.split_once(char::is_whitespace).unwrap_or((info, ""));
    let Some(kind) = UnitKind::parse(directive) else {
        return Ok(None);
    };
    // Legacy directives carry path:declaration on their opening line. Keep their
    // interpretation, but never mistake them for reviewed structured units.
    if argument.contains(':') {
        return Ok(None);
    }
    let id = argument.trim();
    if kind.is_math() && id.is_empty() {
        bail!(
            "{directive} requires a stable unit ID, a :lean: citation, and an authored LaTeX body"
        );
    }
    ensure!(
        valid_id(id),
        "expected one stable unit ID after {directive}"
    );
    let raw = &source[range.clone()];
    let opening_end = raw
        .find('\n')
        .context("unit has no body or closing fence")?
        + 1;
    let closing_start = raw
        .trim_end_matches(['\n', '\r'])
        .rfind('\n')
        .context("unit has no closing fence")?
        + 1;
    let opening = raw[..opening_end].trim_start();
    let marker = opening
        .chars()
        .next()
        .context("unit has no opening fence")?;
    let width = opening.chars().take_while(|c| *c == marker).count();
    let closing = raw[closing_start..].trim();
    ensure!(
        matches!(marker, '`' | '~')
            && closing.chars().all(|c| c == marker)
            && closing.len() >= width,
        "structured unit must have an explicit matching closing fence"
    );
    let contents = &raw[opening_end..closing_start];
    let mut unit = SpecUnit {
        id: id.to_owned(),
        kind,
        draft: false,
        source_path: path.to_owned(),
        range,
        body: String::new(),
        raw: raw.to_owned(),
        lean: vec![],
        rust: vec![],
        tests: vec![],
        uses: vec![],
    };
    let mut seen = BTreeSet::new();
    let mut body_start = 0;
    for line in contents.split_inclusive('\n') {
        let line_text = line.trim_end_matches(['\n', '\r']);
        if !line_text.starts_with(':') {
            break;
        }
        let (option, value) = line_text[1..]
            .split_once(':')
            .context("unit option must have the form :name: value")?;
        ensure!(seen.insert(option), "duplicate :{option}: option");
        let values: Vec<_> = value.split_whitespace().map(str::to_owned).collect();
        ensure!(!values.is_empty(), ":{option}: must not be empty");
        if option == "status" {
            ensure!(
                values == ["draft"],
                ":status: only accepts `draft`; omit it for units ready for correspondence review"
            );
            unit.draft = true;
            body_start += line.len();
            continue;
        }
        let target = match option {
            "lean" => &mut unit.lean,
            "rust" => &mut unit.rust,
            "tests" => &mut unit.tests,
            "uses" => &mut unit.uses,
            _ => bail!("unknown unit option :{option}:"),
        };
        let unique: BTreeSet<_> = values.iter().collect();
        ensure!(
            unique.len() == values.len(),
            "duplicate value in :{option}:"
        );
        *target = values;
        body_start += line.len();
    }
    unit.body = contents[body_start..].trim_matches(['\n', '\r']).to_owned();
    // mdBook expands these even inside fenced code. The packet must contain
    // exactly the authored content, not untracked external substitutions.
    let includes = regex::Regex::new(r"\{\{\s*#(?:include|rustdoc_include|playground)\b")?;
    ensure!(
        !includes.is_match(&unit.raw),
        "mdBook include, rustdoc_include, and playground directives are unsupported inside structured units; write the content directly or cite another unit"
    );
    for event in Parser::new(&unit.body) {
        if let Event::Start(Tag::CodeBlock(CodeBlockKind::Fenced(info))) = event {
            let (directive, argument) = info.split_once(char::is_whitespace).unwrap_or((&info, ""));
            ensure!(
                UnitKind::parse(directive).is_none() || !argument.contains(':'),
                "legacy citation directives cannot nest inside structured units; create a separate unit with :lean: and refer to it with :uses:"
            );
        }
    }
    ensure!(
        !unit.body.trim().is_empty(),
        "unit requires an authored body"
    );
    ensure!(
        !unit.body.starts_with(':'),
        "unit options must immediately follow the opening fence, before the blank line and body"
    );
    ensure!(
        unit.draft || !unit.lean.is_empty() || !unit.rust.is_empty(),
        "unit requires :lean: or :rust: citations; use :status: draft while its formalization is pending"
    );
    ensure!(
        unit.tests.is_empty() || !unit.rust.is_empty(),
        ":tests: requires a :rust: implementation citation"
    );
    ensure!(
        unit.lean.is_empty() || unit.rust.is_empty(),
        "a unit cannot mix :lean: and :rust: citations"
    );
    ensure!(
        !matches!(kind, UnitKind::Theorem | UnitKind::Lemma)
            || !unit.lean.is_empty()
            || (unit.draft && unit.rust.is_empty()),
        "theorem and lemma units require a Lean theorem; Rust tests are not proofs"
    );
    ensure!(
        !matches!(
            kind,
            UnitKind::Judgment
                | UnitKind::Rule
                | UnitKind::Theorem
                | UnitKind::Lemma
                | UnitKind::Example
        ) || unit.lean.is_empty()
            || unit.lean.len() == 1,
        "{} requires exactly one Lean citation",
        kind.label()
    );
    for dependency in &unit.uses {
        ensure!(valid_id(dependency), "invalid dependency ID `{dependency}`");
        ensure!(dependency != id, "unit cannot depend on itself");
    }
    ensure!(
        parse(&unit.body, path)?.is_empty(),
        "named units cannot nest; cite the other unit with :uses: or a link"
    );
    Ok(Some(unit))
}

/// IDs mentioned through anchor-reference roles or local Markdown fragments.
/// Generic heading fragments are returned too; the inventory can distinguish
/// them from unit IDs. Explicit `:uses:` remains independently validated.
pub fn linked_ids(body: &str) -> Result<Vec<String>> {
    links(body, false)
}

/// References that explicitly name a claim, rather than an ordinary heading.
/// These must resolve to units even when no matching ID is in the inventory.
pub fn required_linked_ids(body: &str) -> Result<Vec<String>> {
    links(body, true)
}

fn links(body: &str, required_only: bool) -> Result<Vec<String>> {
    let protected = crate::protect_math(body);
    let mut found = BTreeSet::new();
    for role in crate::roles(&protected)? {
        if !role.definition && !role.lean {
            found.insert(role.id);
        }
    }
    for event in Parser::new(&protected) {
        if let Event::Start(Tag::Link { dest_url, .. }) = event {
            if dest_url.contains(':') || dest_url.starts_with("//") {
                continue;
            }
            if let Some((_, fragment)) = dest_url.split_once('#') {
                if required_only && !fragment.starts_with("claim-") {
                    continue;
                }
                let id = fragment.strip_prefix("claim-").unwrap_or(fragment);
                if valid_id(id) {
                    found.insert(id.to_owned());
                }
            }
        }
    }
    Ok(found.into_iter().collect())
}

/// Parse top-level ID-first units. Legacy citation-first directives are excluded.
pub fn parse(source: &str, path: &str) -> Result<Vec<SpecUnit>> {
    reject_removed_syntax(source, path)?;
    let mut units = Vec::new();
    let mut current = None;
    let mut depth = 0;
    for (event, range) in Parser::new(source).into_offset_iter() {
        match event {
            Event::Start(Tag::CodeBlock(CodeBlockKind::Fenced(info))) if depth == 0 => {
                current = Some((range.start, info.into_string()));
                depth += 1;
            }
            Event::End(TagEnd::CodeBlock) if current.is_some() => {
                let (start, info) = current.take().expect("matched code block");
                let line = source[..start].bytes().filter(|b| *b == b'\n').count() + 1;
                if let Some(unit) = parse_block(source, path, start..range.end, &info)
                    .with_context(|| format!("{path}:{line}"))?
                {
                    ensure!(
                        !units.iter().any(|other: &SpecUnit| other.id == unit.id),
                        "{path}:{line}: duplicate unit ID `{}`",
                        unit.id
                    );
                    units.push(unit);
                }
                depth -= 1;
            }
            Event::Start(_) => depth += 1,
            Event::End(_) => depth -= 1,
            _ => {}
        }
    }
    Ok(units)
}

/// Retired authoring syntax is an error even outside strict chapters or inside
/// lists and quotations. Ordinary code samples and escaped roles remain literal.
fn reject_removed_syntax(source: &str, path: &str) -> Result<()> {
    crate::roles(&crate::protect_math(source)).with_context(|| path.to_owned())?;
    for block in crate::directive_blocks(source) {
        let directive = block.info.split_whitespace().next().unwrap_or("");
        let line = source[..block.range.start]
            .bytes()
            .filter(|byte| *byte == b'\n')
            .count()
            + 1;
        ensure!(
            !directive.starts_with("{obligation}"),
            "{path}:{line}: {{obligation}} has been removed; use a definition, theorem, lemma, or example with :status: draft when formalization is pending"
        );
        if matches!(
            directive,
            "{definition}" | "{theorem}" | "{lemma}" | "{example}"
        ) {
            reject_removed_syntax(&block.body, path)?;
        }
    }
    Ok(())
}

/// Strict chapters contain only headings and whitespace outside named units.
/// Callers opt chapters into this policy explicitly; legacy chapters are not
/// silently treated as covered by evidence for unrelated units.
pub fn validate_coverage(source: &str, path: &str) -> Result<()> {
    let units = parse(source, path)?;
    let mut allowed: Vec<_> = units.iter().map(|unit| unit.range.clone()).collect();
    for (event, range) in Parser::new(source).into_offset_iter() {
        if matches!(event, Event::Start(Tag::Heading { .. })) {
            allowed.push(range);
        }
    }
    if let Some((offset, _)) = source.char_indices().find(|(offset, character)| {
        !character.is_whitespace() && !allowed.iter().any(|range| range.contains(offset))
    }) {
        let line = source[..offset].bytes().filter(|b| *b == b'\n').count() + 1;
        bail!("{path}:{line}: content outside a named unit; put semantic prose, mathematics, and examples inside their unit");
    }
    Ok(())
}

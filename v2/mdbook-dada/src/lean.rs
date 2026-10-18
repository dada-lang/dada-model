//! Extraction of a deliberately restricted, line-oriented Lean declaration style.
use anyhow::{ensure, Context, Result};
use std::collections::HashSet;
use std::path::{Component, Path};

// Mask comments and strings while retaining byte offsets and newlines.
fn mask(source: &str) -> Result<String> {
    Ok(scan(source)?.code)
}

// Retain the offsets of real line comments so source anchors cannot be forged
// by text inside strings or nested block comments.
fn mask_and_comments(source: &str) -> Result<(String, Vec<usize>)> {
    let scanned = scan(source)?;
    Ok((scanned.code, scanned.line_comments))
}

struct Scanned {
    code: String,
    line_comments: Vec<usize>,
    // End of the final code token, literal, or attached inline comment. Unlike
    // `code.trim_end()`, this retains a body ending in a string literal.
    content_end: usize,
}

fn scan(source: &str) -> Result<Scanned> {
    let bytes = source.as_bytes();
    let mut output = bytes.to_vec();
    let mut comments = Vec::new();
    let mut content_end = 0;
    let mut i = 0;
    while i < bytes.len() {
        let start = i;
        let mut comment = false;
        if bytes.get(i..i + 2) == Some(b"/-") {
            comment = true;
            i += 2;
            let mut depth = 1;
            while i < bytes.len() && depth > 0 {
                match bytes.get(i..i + 2) {
                    Some(b"/-") => {
                        depth += 1;
                        i += 2;
                    }
                    Some(b"-/") => {
                        depth -= 1;
                        i += 2;
                    }
                    _ => i += 1,
                }
            }
            ensure!(depth == 0, "unterminated Lean comment");
        } else if bytes.get(i..i + 2) == Some(b"--") {
            comment = true;
            comments.push(i);
            i = source[i..].find('\n').map_or(bytes.len(), |n| i + n);
        } else if let Some((quote, hashes)) = raw_string_start(source, i) {
            let closing = format!("\"{}", "#".repeat(hashes));
            let tail = quote + 1;
            i = tail
                + source[tail..]
                    .find(&closing)
                    .context("unterminated Lean raw string")?
                + closing.len();
        } else if let Some(end) = character_end(source, i) {
            i = end;
        } else if source[i..].starts_with('«') {
            i += source[i..]
                .find('»')
                .context("unterminated Lean quoted identifier")?
                + '»'.len_utf8();
        } else if bytes[i] == b'"' {
            i += 1;
            loop {
                ensure!(i < bytes.len(), "unterminated Lean string");
                match bytes[i] {
                    b'"' => {
                        i += 1;
                        break;
                    }
                    b'\\' => i += 2,
                    _ => i += 1,
                }
            }
        } else {
            // Keep UTF-8 boundaries for the character-literal lookahead below.
            let c = source[i..].chars().next().unwrap();
            i += c.len_utf8();
            if !c.is_whitespace() {
                content_end = i;
            }
            continue;
        }
        if !comment || !source[content_end..start].contains('\n') {
            // Keep comments beginning on the final code line, including a
            // block comment continuing onto later lines. Standalone comments
            // after the body belong to neither the selected declaration nor
            // its source extent. Comments before later code remain intact.
            content_end = i;
        }
        for byte in &mut output[start..i] {
            if *byte != b'\n' {
                *byte = b' ';
            }
        }
    }
    Ok(Scanned {
        code: String::from_utf8(output)?,
        line_comments: comments,
        content_end,
    })
}

fn follows_identifier(source: &str, offset: usize) -> bool {
    source[..offset]
        .chars()
        .next_back()
        .is_some_and(|c| c.is_alphanumeric() || matches!(c, '_' | '\''))
}

// Lean raw strings use r"...", r#"..."#, r##"..."##, etc. Their
// contents have neither escapes nor comments, including any embedded quotes.
fn raw_string_start(source: &str, start: usize) -> Option<(usize, usize)> {
    let bytes = source.as_bytes();
    if bytes[start] != b'r' || follows_identifier(source, start) {
        return None;
    }
    let mut quote = start + 1;
    while bytes.get(quote) == Some(&b'#') {
        quote += 1;
    }
    (bytes.get(quote) == Some(&b'"')).then_some((quote, quote - start - 1))
}

fn character_end(source: &str, start: usize) -> Option<usize> {
    let bytes = source.as_bytes();
    if bytes[start] != b'\'' || follows_identifier(source, start) {
        return None;
    }
    let mut end = start + 1;
    let character = source[end..].chars().next()?;
    end += character.len_utf8();
    if character == '\\' {
        end += match bytes.get(end)? {
            b'x' => 3,
            b'u' => 5,
            _ => 1,
        };
    }
    (bytes.get(end) == Some(&b'\'')).then_some(end + 1)
}

pub fn extract(source: &str, name: &str) -> Result<String> {
    extract_declaration(source, name, Selection::Type)
}

fn extract_theorem(source: &str, name: &str) -> Result<String> {
    extract_declaration(source, name, Selection::Theorem)
}

fn extract_definition(source: &str, name: &str) -> Result<String> {
    extract_declaration(source, name, Selection::Definition)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Selection {
    Type,
    Theorem,
    Definition,
}

fn extract_declaration(source: &str, name: &str, selection: Selection) -> Result<String> {
    let simple_name = |component: &str| {
        !component.is_empty() && component.chars().all(|c| c.is_alphanumeric() || c == '_')
    };
    if selection != Selection::Type {
        ensure!(
            name.split('.').all(simple_name),
            "use a declaration name with nonempty identifier components separated by single dots"
        );
    } else {
        ensure!(
            simple_name(name),
            "use a simple unqualified declaration name"
        );
    }
    let masked = mask(source)?;
    ensure!(
        !masked.lines().any(|l| l.trim() == "mutual"),
        "mutual declarations are unsupported"
    );
    let mut found = Vec::new();
    let mut offset = 0;
    let lines: Vec<_> = masked
        .split_inclusive('\n')
        .map(|line| {
            let start = offset;
            offset += line.len();
            (start, line)
        })
        .collect();
    for (i, &(start, line)) in lines.iter().enumerate() {
        let words: Vec<_> = line.split_whitespace().collect();
        if selection == Selection::Definition {
            let declaration: Vec<_> = words
                .iter()
                .copied()
                .skip_while(|word| {
                    matches!(
                        *word,
                        "private" | "protected" | "noncomputable" | "unsafe" | "partial" | "nonrec"
                    )
                })
                .collect();
            // Literal names are intentionally not resolved through namespaces.
            // A same-named declaration of the wrong kind must not disappear
            // from an otherwise ambiguous citation.
            if declaration.get(1) == Some(&name)
                && matches!(
                    declaration.first(),
                    Some(
                        &"def"
                            | &"abbrev"
                            | &"structure"
                            | &"inductive"
                            | &"theorem"
                            | &"lemma"
                            | &"axiom"
                            | &"opaque"
                            | &"constant"
                            | &"class"
                    )
                )
            {
                ensure!(
                    declaration.len() == words.len(),
                    "declaration modifiers are unsupported"
                );
                ensure!(
                    matches!(declaration.first(), Some(&"def" | &"abbrev" | &"structure" | &"inductive")),
                    "definition citations must select def, abbrev, structure, or inductive declarations"
                );
            }
        }
        if words.get(1) != Some(&name) {
            continue;
        }
        let supported = match selection {
            Selection::Theorem => words.first() == Some(&"theorem"),
            Selection::Type => {
                matches!(words.first(), Some(&"inductive" | &"structure" | &"abbrev"))
            }
            Selection::Definition => matches!(
                words.first(),
                Some(&"def" | &"inductive" | &"structure" | &"abbrev")
            ),
        };
        if !supported {
            continue;
        }
        ensure!(
            !line.starts_with(char::is_whitespace),
            "selected Lean declarations must begin at column zero"
        );
        if let Some((_, previous)) = lines[..i].iter().rev().find(|(_, l)| !l.trim().is_empty()) {
            ensure!(
                !previous.trim_start().starts_with("@["),
                "declaration attributes are unsupported"
            );
        }
        if let Some((_, boundary)) = lines[i + 1..]
            .iter()
            .find(|(_, l)| !l.trim().is_empty() && !l.starts_with(char::is_whitespace))
        {
            let mut words = boundary.split_whitespace();
            let first = words.next().unwrap_or("");
            let mut word = first;
            while matches!(
                word,
                "private" | "protected" | "noncomputable" | "unsafe" | "partial" | "nonrec"
            ) {
                word = words.next().unwrap_or("");
            }
            ensure!(
                (word == first
                    || matches!(
                        word,
                        "inductive" | "structure" | "abbrev" | "def" | "theorem" | "instance"
                    ))
                    && matches!(
                        word,
                        "inductive"
                            | "structure"
                            | "abbrev"
                            | "def"
                            | "theorem"
                            | "lemma"
                            | "example"
                            | "instance"
                            | "end"
                            | "namespace"
                            | "section"
                            | "variable"
                            | "open"
                            | "#check"
                    ),
                "unsupported declaration boundary `{}`; continuation lines must be indented",
                boundary.trim()
            );
        }
        let end = lines[i + 1..]
            .iter()
            .find(|(_, l)| !l.trim().is_empty() && !l.starts_with(char::is_whitespace))
            .map(|(n, _)| *n)
            .unwrap_or(source.len());
        let body = &source[start..end];
        let text = &body[..scan(body)?.content_end];
        if selection != Selection::Type {
            ensure!(
                command_pattern()?.find_iter(&masked[start..end]).count() == 1,
                "selected declaration must contain no other commands, even when indented"
            );
        }
        if selection == Selection::Theorem {
            ensure!(
                has_definition_body(&masked[start..end]),
                "theorem must include its proof body (`:=`)"
            );
        } else if selection == Selection::Definition && words[0] == "def" {
            ensure!(
                has_named_definition_body(&masked[start..end])?,
                "definition must include a body (`:=`, `where`, or indented equations with `=>`)"
            );
        } else if words[0] != "abbrev" {
            ensure!(
                line.contains("where"),
                "declaration header must contain `where` on its first line"
            );
        } else {
            if selection == Selection::Definition {
                ensure!(
                    has_definition_body(&masked[start..end]),
                    "abbreviation must include a body (`:=`)"
                );
            } else {
                ensure!(line.contains(":="), "abbreviation header must contain `:=`");
            }
        }
        found.push(text.to_owned());
    }
    ensure!(
        found.len() == 1,
        "expected one supported declaration `{name}`, found {}",
        found.len()
    );
    Ok(found.remove(0))
}

fn read_source(root: &Path, target: &str) -> Result<(String, String)> {
    let (file, name) = target
        .rsplit_once(':')
        .context("expected path:Declaration")?;
    let mut relative = std::path::PathBuf::from(file);
    ensure!(
        !file.is_empty()
            && relative
                .components()
                .all(|c| matches!(c, Component::Normal(_))),
        "Lean path must be relative without traversal"
    );
    if relative.extension().is_none() {
        relative.set_extension("lean");
    }
    ensure!(
        relative.extension().is_some_and(|e| e == "lean"),
        "expected a .lean file"
    );
    let canonical_root = root.canonicalize().context("Lean source directory")?;
    let path = canonical_root
        .join(&relative)
        .canonicalize()
        .with_context(|| format!("Lean file {file}"))?;
    ensure!(
        path.starts_with(&canonical_root),
        "Lean source escapes configured directory"
    );
    let source = std::fs::read_to_string(path)?;
    Ok((source, name.to_owned()))
}

fn highlighted(declaration: &str) -> Result<String> {
    let masked = mask(declaration)?;
    let keywords = regex::Regex::new(
        r"\b(inductive|structure|abbrev|def|theorem|where|deriving|example|by|let|have|show|exact)\b",
    )?;
    let mut html = String::new();
    let mut last = 0;
    for m in keywords.find_iter(&masked) {
        html.push_str(&crate::escape(&declaration[last..m.start()]));
        html.push_str(&format!(
            "<span class=\"lean-keyword\">{}</span>",
            &declaration[m.range()]
        ));
        last = m.end();
    }
    html.push_str(&crate::escape(&declaration[last..]));
    Ok(html.replace('\n', "&#10;"))
}

fn valid_anchor_name(name: &str) -> bool {
    name.as_bytes()
        .first()
        .is_some_and(u8::is_ascii_alphanumeric)
        && name
            .bytes()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, b'_' | b'.' | b'-'))
}

fn has_definition_body(code: &str) -> bool {
    let mut delimiters = Vec::new();
    let mut chars = code.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '(' | '{' | '[' | '⦃' => delimiters.push(c),
            ')' | '}' | ']' | '⦄' => {
                delimiters.pop();
            }
            ':' if delimiters.is_empty() && chars.peek() == Some(&'=') => return true,
            _ => {}
        }
    }
    false
}

// In addition to `:=`, a named definition can use a structure literal's
// `where` or equations. This is a source-style check, not Lean elaboration:
// equation arms start on indented lines and put `=>` on their first line.
// In particular, default binder values do not supply a declaration body.
fn has_named_definition_body(code: &str) -> Result<bool> {
    if has_definition_body(code) {
        return Ok(true);
    }
    let mut delimiters = Vec::new();
    for (offset, c) in code.char_indices() {
        match c {
            '(' | '{' | '[' | '⦃' => delimiters.push(c),
            ')' | '}' | ']' | '⦄' => {
                delimiters.pop();
            }
            'w' if delimiters.is_empty()
                && !follows_identifier(code, offset)
                && code[offset..].starts_with("where")
                && !code[offset + "where".len()..]
                    .chars()
                    .next()
                    .is_some_and(|c| c.is_alphanumeric() || matches!(c, '_' | '\'')) =>
            {
                return Ok(true);
            }
            '|' if delimiters.is_empty()
                && code[..offset]
                    .rsplit_once('\n')
                    .is_some_and(|(_, prefix)| !prefix.is_empty() && prefix.trim().is_empty()) =>
            {
                let arm = code[offset..].lines().next().unwrap_or("");
                ensure!(
                    arm.contains("=>"),
                    "equation arms must put `=>` on their first line"
                );
                return Ok(true);
            }
            _ => {}
        }
    }
    Ok(false)
}

fn command_pattern() -> Result<regex::Regex> {
    Ok(regex::Regex::new(
        r"(?m)^[ \t]*(?:@\[|#|(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|local|scoped)[ \t]+)*(?:example|def|theorem|lemma|abbrev|opaque|axiom|constant|constants|inductive|structure|class|instance|namespace|section|end|variable|variables|universe|universes|import|open|export|attribute|macro|macro_rules|syntax|elab|elab_rules|notation|infix|infixl|infixr|prefix|postfix|initialize|builtin_initialize|mutual)(?:[ \t(:{\[]|$))",
    )?)
}

fn extract_example(source: &str, name: &str) -> Result<String> {
    ensure!(
        valid_anchor_name(name),
        "invalid Lean example anchor `{name}`"
    );
    let (masked, comments) = mask_and_comments(source)?;
    let mut names = HashSet::new();
    let mut open = None;
    let mut selected = None;
    for offset in comments {
        let line_start = source[..offset].rfind('\n').map_or(0, |n| n + 1);
        if !source[line_start..offset].trim().is_empty() {
            continue;
        }
        let line_end = source[offset..]
            .find('\n')
            .map_or(source.len(), |n| offset + n);
        let comment = source[offset + 2..line_end].trim();
        let (end, anchor) = if let Some(anchor) = comment.strip_prefix("ANCHOR:") {
            (false, anchor.trim())
        } else if let Some(anchor) = comment.strip_prefix("ANCHOR_END:") {
            (true, anchor.trim())
        } else {
            continue;
        };
        ensure!(
            valid_anchor_name(anchor),
            "invalid Lean example anchor `{anchor}`"
        );
        if end {
            let (opened, start) = open.take().with_context(|| {
                format!("Lean example anchor `{anchor}` ends without a matching start")
            })?;
            ensure!(
                opened == anchor,
                "Lean example anchor `{opened}` ends with mismatched `{anchor}`"
            );
            if anchor == name {
                selected = Some((start..line_start, (line_end + 1).min(source.len())));
            }
        } else {
            ensure!(open.is_none(), "nested Lean example anchor `{anchor}`");
            ensure!(
                names.insert(anchor),
                "duplicate Lean example anchor `{anchor}`"
            );
            open = Some((anchor, (line_end + 1).min(source.len())));
        }
    }
    if let Some((anchor, _)) = open {
        anyhow::bail!("unterminated Lean example anchor `{anchor}`");
    }
    let (range, after) =
        selected.with_context(|| format!("missing Lean example anchor `{name}`"))?;
    if let Some(next) = masked[after..].lines().find(|line| !line.trim().is_empty()) {
        ensure!(
            !next.starts_with(char::is_whitespace),
            "Lean example anchor `{name}` ends before an indented continuation; place the end marker after the complete example and start the next command at column zero"
        );
    }
    let mut lines = masked[range.clone()]
        .lines()
        .filter(|line| !line.trim().is_empty());
    let header = lines
        .next()
        .with_context(|| format!("Lean example anchor `{name}` is empty"))?;
    let keyword = header
        .split(|c: char| c.is_whitespace() || matches!(c, ':' | '(' | '{' | '['))
        .next();
    ensure!(
        keyword == Some("example"),
        "Lean example anchor `{name}` must contain a column-zero anonymous `example`"
    );
    ensure!(
        lines.all(|line| line.starts_with(char::is_whitespace)),
        "Lean example anchor `{name}` must contain exactly one `example`; continuation lines must be indented"
    );
    // Lean allows sibling commands to be indented. Indentation alone therefore
    // cannot establish that a marked span contains only the selected example.
    // This restricted source style excludes command declarations inside proofs.
    let command = command_pattern()?;
    let declaration_count = command.find_iter(&masked[range.clone()]).count();
    let example_count = regex::Regex::new(r"\bexample\b")?
        .find_iter(&masked[range.clone()])
        .count();
    ensure!(
        declaration_count == 1 && example_count == 1,
        "Lean example anchor `{name}` must contain exactly one `example` and no other commands, even when indented"
    );
    ensure!(
        has_definition_body(&masked[range.clone()]),
        "Lean example anchor `{name}` must include the example body (`:=`)"
    );
    // Preserve code indentation while excluding surrounding blank lines and the
    // anchor markers. Comments documenting the example remain visible.
    Ok(source[range].trim_matches(['\n', '\r']).to_owned())
}

/// Select a marked anonymous Lean example and render its cited source.
/// This checks the marker structure, not Lean elaboration or prose agreement.
pub fn example_source(root: &Path, target: &str) -> Result<String> {
    let (source, anchor) = read_source(root, target)?;
    let example = extract_example(&source, &anchor).with_context(|| target.to_owned())?;
    Ok(format!(
        "<figcaption>{}</figcaption><pre><code class=\"language-lean\">{}</code></pre>",
        crate::escape(target),
        highlighted(&example)?
    ))
}

/// Select exactly one named theorem, preserving its statement and complete proof.
/// Theorem and lemma Markdown blocks share this source-selection contract.
pub fn theorem_source(root: &Path, target: &str) -> Result<String> {
    let (source, name) = read_source(root, target)?;
    let theorem = extract_theorem(&source, &name).with_context(|| target.to_owned())?;
    Ok(format!(
        "<figcaption>{}</figcaption><pre><code class=\"language-lean\">{}</code></pre>",
        crate::escape(target),
        highlighted(&theorem)?
    ))
}

/// Select the complete declarations associated with an authored definition.
/// Citations name declarations literally; enclosing namespaces are not inferred.
pub fn definition_source(root: &Path, targets: &str) -> Result<String> {
    let targets: Vec<_> = targets.split_whitespace().collect();
    ensure!(
        !targets.is_empty(),
        "definition requires at least one opening-line citation"
    );
    let mut output = String::new();
    for target in targets {
        let (source, name) = read_source(root, target)?;
        let declaration = extract_definition(&source, &name).with_context(|| target.to_owned())?;
        output.push_str(&format!(
            "<figcaption>{}</figcaption><pre><code class=\"language-lean\">{}</code></pre>",
            crate::escape(target),
            highlighted(&declaration)?
        ));
    }
    Ok(output)
}

fn selector(rendered: &str, source: &str, group: &str, label: &str) -> String {
    let selector = crate::selector_header(label, None, group, "grammar", "Lean");
    format!("<figure class=\"lean-declaration lean-group\">{selector}<div class=\"lean-grammar\">{rendered}</div><div class=\"lean-source\">{source}<p>Imports, namespaces and section variables remain in the source file.</p></div></figure>")
}

// Select constructor source by its name and indentation, without interpreting
// its binders, premises, or result. Nested match alternatives are not cases.
fn extract_case(declaration: &str, case: &str) -> Result<String> {
    ensure!(
        !case.is_empty() && case.chars().all(|c| c.is_alphanumeric() || c == '_'),
        "use a simple constructor name"
    );
    let masked = mask(declaration)?;
    let header = declaration
        .lines()
        .next()
        .context("missing declaration header")?;
    ensure!(
        header.starts_with("inductive "),
        "rule citation must select an inductive constructor"
    );
    let mut offset = 0;
    let mut candidates = Vec::new();
    for line in masked.split_inclusive('\n') {
        let trimmed = line.trim_start();
        let indent = line.len() - trimmed.len();
        if let Some(row) = trimmed.strip_prefix('|') {
            let name = row
                .trim_start()
                .split(|c: char| c.is_whitespace() || matches!(c, ':' | '(' | '{' | '['))
                .next()
                .unwrap_or("");
            candidates.push((offset, indent, name));
        }
        offset += line.len();
    }
    let indent = candidates
        .iter()
        .map(|(_, indent, _)| *indent)
        .min()
        .context("inductive has no constructors")?;
    let cases: Vec<_> = candidates
        .into_iter()
        .filter(|(_, i, _)| *i == indent)
        .collect();
    let found: Vec<_> = cases
        .iter()
        .enumerate()
        .filter(|(_, (_, _, n))| *n == case)
        .collect();
    ensure!(
        found.len() == 1,
        "expected one constructor `{case}`, found {}",
        found.len()
    );
    let (index, (start, _, _)) = found[0];
    let end = cases
        .get(index + 1)
        .map(|(start, _, _)| *start)
        .unwrap_or(declaration.len());
    // A comment introducing the next declaration is not part of this case.
    let end = masked[..end].trim_end().len();
    Ok(format!("{header}\n{}", declaration[*start..end].trim_end()))
}

/// Which source selections accompany an authored mathematical block.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum View {
    Grammar,
    Judgment,
    Rule,
}

/// Check source citations and pair authored LaTeX with those source excerpts.
/// No mathematical syntax is generated from, or compared with, the Lean source.
pub fn render_authored(
    root: &Path,
    targets: &str,
    body: &str,
    view: View,
    group: &str,
) -> Result<String> {
    let targets: Vec<_> = targets.split_whitespace().collect();
    ensure!(!targets.is_empty(), "expected Lean citations on the directive opening line; use ```{{grammar}} path:Name with authored LaTeX in the body");
    ensure!(
        view == View::Grammar || targets.len() == 1,
        "judgment and rule directives require exactly one opening-line citation"
    );
    ensure!(
        !body.trim().is_empty(),
        "authored math directive requires a LaTeX body"
    );
    let mut source = String::new();
    for target in targets {
        let (file, selected) = read_source(root, target)?;
        let (name, case) = if view == View::Rule {
            let (name, case) = selected
                .rsplit_once('.')
                .context("rule expects path:Judgment.constructor")?;
            (name, Some(case))
        } else {
            (selected.as_str(), None)
        };
        let declaration = extract(&file, name).with_context(|| target.to_owned())?;
        ensure!(
            !matches!(view, View::Judgment | View::Rule) || declaration.starts_with("inductive "),
            "judgment and rule citations must select inductive declarations"
        );
        let declaration = if let Some(case) = case {
            extract_case(&declaration, case)?
        } else {
            declaration
        };
        source.push_str(&format!(
            "<figcaption>{}</figcaption><pre><code class=\"language-lean\">{}</code></pre>",
            crate::escape(target),
            highlighted(&declaration)?
        ));
    }
    // Keep blank lines inside the raw HTML block so Markdown cannot reinterpret
    // the authored TeX. Escaping also keeps TeX text from becoming HTML markup.
    let tex = crate::escape(body.trim()).replace('\n', "&#10;");
    let rendered = format!("<div class=\"math-display\">\\[{tex}\\]</div>");
    let label = match view {
        View::Grammar => "Grammar",
        View::Judgment => "Judgment",
        View::Rule => "Rule",
    };
    Ok(selector(&rendered, &source, group, label))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn definitions_select_complete_equations_structure_literals_and_multiline_bodies() {
        let source = "namespace Outer\ndef State.initial : State Primitive :=\n  .state FiniteMap.empty FiniteMap.empty\ndef readSlot : State Primitive → Place → Option Slot\n  | .state _ variables, .variable id => variables.lookup id\n  | .state objects _, .field id name => do\n      let .aggregate fields ← objects.lookup id | none\n      fields.lookup name\ndef empty : Store where\n  entries := []\n  uniqueKeys := by\n    exact List.nodup_nil\nabbrev Value\n    (α : Type) :=\n  Option α\nend Outer\n";
        assert_eq!(
            extract_definition(source, "State.initial").unwrap(),
            "def State.initial : State Primitive :=\n  .state FiniteMap.empty FiniteMap.empty"
        );
        let read = extract_definition(source, "readSlot").unwrap();
        assert!(read.contains("  | .state _ variables"));
        assert!(read.ends_with("      fields.lookup name"));
        assert!(!read.contains("def empty"));
        assert!(extract_definition(source, "empty")
            .unwrap()
            .ends_with("    exact List.nodup_nil"));
        assert!(extract_definition(source, "Value")
            .unwrap()
            .ends_with("  Option α"));
        assert!(extract_definition(source, "initial").is_err());
        assert!(extract_definition(source, "Outer.State.initial").is_err());
        // The math-only grammar directive retains its original type contract.
        assert!(extract(source, "readSlot").is_err());
        assert!(extract(source, "Value").is_err());
        for source in [
            "structure Foo where\n  n : Nat",
            "inductive Foo where\n  | zero\n  | succ (previous : Foo)",
            "abbrev Foo := Nat",
        ] {
            assert_eq!(extract_definition(source, "Foo").unwrap(), source);
        }
    }

    #[test]
    fn definition_selection_ignores_comment_and_literal_decoys() {
        let source = r###"/- def selected := 0 /- def selected := 1 -/ -/
def text := r##"
def selected := 2
"##
def other := "
def selected := 3
"
-- def selected := 4
def selected : Nat :=
  let text := "def selected := 5"
  let c := '"'
  6
def next := 7
"###;
        let selected = extract_definition(source, "selected").unwrap();
        assert!(selected.starts_with("def selected : Nat :=\n"));
        assert!(selected.ends_with("  6"));
        assert!(selected.contains("let text"));
        assert!(!selected.contains("def next"));
    }

    #[test]
    fn declaration_extent_excludes_trailing_comments_but_keeps_body_and_inline_comments() {
        let selected = "def selected : Nat :=\n  -- Explain this body.\n  let n := 1\n  /- Explain the result, with /- nesting -/. -/\n  n -- Keep this inline comment.";
        for trailer in [
            "\n\n-- The next definition does something else.\n\n",
            "\n/- The next definition.\n   /- Nested comment. -/\n-/\n\n",
            "\n  -- A trailing comment is not a continuation.\n  /- Nor is this block. -/\n",
        ] {
            for next in ["def next := 2\n", ""] {
                let source = format!("{selected}{trailer}{next}");
                assert_eq!(extract_definition(&source, "selected").unwrap(), selected);
            }
        }
        let block_inline =
            "def selected :=\n  1 /- An attached comment\n       may cross lines. -/";
        assert_eq!(
            extract_definition(
                &format!("{block_inline}\n-- Next definition.\ndef next := 2"),
                "selected"
            )
            .unwrap(),
            block_inline
        );
    }

    #[test]
    fn declaration_extent_keeps_final_literal_expressions_and_comment_text_inside_literals() {
        for body in [
            "  \"text\"",
            "  \"-- literal, not a comment\" -- Actual inline comment.",
            "  \"first line\n-- literal line\n/- still literal -/\nlast line\"",
            "  r#\"first line\n-- literal line\n/- still literal -/\nlast line\"#",
            "  'α'",
        ] {
            let selected = format!("def selected :=\n{body}");
            let source = format!("{selected}\n\n/- A comment for next. -/\ndef next := 0\n");
            assert_eq!(extract_definition(&source, "selected").unwrap(), selected);
        }
    }

    #[test]
    fn definitions_reject_unsupported_incomplete_and_ambiguous_sources() {
        for source in [
            "theorem selected : True := by trivial",
            "axiom selected : Nat",
            "opaque selected : Nat := 0",
            "example : Nat := 0",
            "private def selected := 0",
            "@[simp]\ndef selected := 0",
            "  def selected := 0",
            "def selected : Nat",
            "def selected (n : Nat := 0) : Nat",
            "def selected : Nat -- := 0",
            "def selected : Nat /- where -/",
            "def selected : Nat :=\n0",
            "def selected : Nat → Nat\n| n => n",
            "def selected : Nat → Nat\n  | n\n    => n",
            "def selected := 0\ntermination_by 0",
            "def selected := 0\n  def sibling := 1",
            "def selected := 0\n  theorem sibling : True := by trivial",
            "def selected := 0\nmystery next",
            "def selected := 0\nnamespace Nested\ndef selected := 1\nend Nested",
            "namespace A\ndef selected := 0\nend A\nnamespace B\ndef selected := 1\nend B",
            "namespace A\ndef selected := 0\nend A\nnamespace B\ntheorem selected : True := by trivial\nend B",
            "namespace A\ndef selected := 0\nend A\nnamespace B\nprivate def selected := 1\nend B",
            "mutual\ndef selected := 0\nend",
        ] {
            assert!(extract_definition(source, "selected").is_err(), "{source}");
        }
        for name in [".selected", "selected.", "N..selected", "N:selected"] {
            assert!(extract_definition(&format!("def {name} := 0"), name).is_err());
        }
    }

    #[test]
    fn selects_complete_named_theorems_without_comment_or_string_decoys() {
        let source = r#"-- theorem preserves : False := by sorry
def text := "theorem preserves : False := by sorry"
/- theorem preserves : False := by sorry -/
theorem preserves
    (n : Nat)
    (h : n = 0) : n = 0 := by
  have same : n = 0 := h
  exact same
theorem next : True := by trivial
"#;
        let selected = extract_theorem(source, "preserves").unwrap();
        assert!(selected.starts_with("theorem preserves\n"));
        assert!(selected.ends_with("  exact same"));
        assert!(!selected.contains("sorry"));
        assert!(!selected.contains("theorem next"));
        assert_eq!(
            extract_theorem(source, "next").unwrap(),
            "theorem next : True := by trivial"
        );
        assert!(extract(source, "preserves").is_err());
    }

    #[test]
    fn qualified_theorem_names_match_only_the_literal_declaration_name() {
        let source = "namespace Outer\ntheorem MoveReference.dependent_follows : True := by\n  trivial\ntheorem other : True := by trivial\nend Outer\n";
        assert_eq!(
            extract_theorem(source, "MoveReference.dependent_follows").unwrap(),
            "theorem MoveReference.dependent_follows : True := by\n  trivial"
        );
        assert!(extract_theorem(source, "dependent_follows").is_err());
        assert!(extract_theorem(source, "Outer.MoveReference.dependent_follows").is_err());
        assert!(extract_theorem(source, "Outer.other").is_err());
        assert!(extract_theorem(source, "other").is_ok());
        assert!(extract(
            "inductive Qualified.Type where\n  | constructor",
            "Qualified.Type"
        )
        .is_err());
    }

    #[test]
    fn rejects_malformed_theorem_name_components_even_when_source_matches() {
        for name in ["", ".selected", "selected.", "N..selected", "N:selected"] {
            let source = format!("theorem {name} : True := by trivial");
            let error = extract_theorem(&source, name).unwrap_err().to_string();
            assert!(error.contains("nonempty identifier components"), "{name}");
        }
    }

    #[test]
    fn declaration_boundaries_accept_modifiers_only_before_supported_declarations() {
        let selected = "theorem selected : True := by\n  trivial";
        for next in [
            "private theorem hidden : True := by trivial",
            "private def helper := 0",
            "protected theorem nested : True := by trivial",
            "private noncomputable def choice := 0",
        ] {
            assert_eq!(
                extract_theorem(&format!("{selected}\n{next}\n"), "selected").unwrap(),
                selected
            );
        }
        for next in [
            "private",
            "private mystery next",
            "private end",
            "mystery theorem next : True := by trivial",
        ] {
            assert!(
                extract_theorem(&format!("{selected}\n{next}\n"), "selected").is_err(),
                "{next}"
            );
        }
        assert!(extract_theorem(
            &format!("{selected}\n  private theorem hidden : True := by trivial"),
            "selected"
        )
        .is_err());
    }

    #[test]
    fn rejects_wrong_kind_ambiguous_and_incomplete_theorem_selections() {
        for source in [
            "def selected : True := by trivial",
            "axiom selected : True",
            "example : True := by trivial",
            "inductive selected : Prop where\n  | intro",
            "theorem selected : True := by trivial\ntheorem selected : True := by trivial",
            "theorem selected : True",
            "theorem selected (n : Nat := 0) : True",
            "@[simp]\ntheorem selected : True := by trivial",
            "  theorem selected : True := by trivial",
            "theorem selected : True := by\ntrivial",
            "theorem selected : True := by trivial\n  theorem next : True := by trivial",
            "theorem selected : True := by trivial\n  def next := 0",
        ] {
            assert!(extract_theorem(source, "selected").is_err(), "{source}");
        }
        assert!(extract_theorem("theorem selected : True := by trivial", "missing").is_err());
        assert!(extract_theorem("theorem selected : True := by trivial", "N.selected").is_err());
    }

    #[test]
    fn selects_one_anonymous_example_with_comments_and_multiline_proof() {
        let source = "namespace Tests\n-- ANCHOR: variables.alloc-0\n/- A checked example, with a nested /- comment -/. -/\nexample\n    (n : Nat) :\n    n = n := by\n  rfl\n-- ANCHOR_END: variables.alloc-0\nend Tests\n";
        let example = extract_example(source, "variables.alloc-0").unwrap();
        assert!(example.starts_with("/- A checked example"));
        assert!(example.contains("    n = n := by\n  rfl"));
        assert!(!example.contains("ANCHOR"));
        assert!(!example.contains("namespace"));
        assert!(!example.contains("end Tests"));
        assert!(highlighted(&example)
            .unwrap()
            .contains("<span class=\"lean-keyword\">example</span>"));
        assert!(extract_example(
            "-- ANCHOR: direct\nexample : Nat := 0\n-- ANCHOR_END: direct",
            "direct"
        )
        .is_ok());
    }

    #[test]
    fn ignores_anchor_decoys_in_strings_block_comments_and_inline_comments() {
        let source = r#"/-
-- ANCHOR: absent
  /- -- ANCHOR_END: mismatched -/
-- ANCHOR: actual
-/
def text := "
-- ANCHOR_END: absent
-- ANCHOR: actual
"
def inline := 0 -- ANCHOR: actual
-- A comment containing -- ANCHOR: actual
-- ANCHOR: actual
example : "-- ANCHOR_END: actual" = "-- ANCHOR_END: actual" := by
  rfl
-- ANCHOR_END: actual
"#;
        let example = extract_example(source, "actual").unwrap();
        assert!(example.starts_with("example :"));
        assert!(example.contains("  rfl"));
        assert!(extract_example(source, "absent").is_err());
    }

    #[test]
    fn masks_raw_strings_and_character_literals_without_masking_identifier_primes() {
        let source = r###"def text := r##"
"#
-- ANCHOR: decoy
example : True := by trivial
-- ANCHOR_END: decoy
"
"##
def quote : Char := '"'
def escapedQuote : Char := '\''
def unicode : Char := 'α'
def hex : Char := '\x22'
def wideHex : Char := '\u0022'
def raw := r"backslash \"
def state' := 0
def «
-- ANCHOR: identifier-decoy
example : True := by trivial
-- ANCHOR_END: identifier-decoy
» := 0
-- ANCHOR: actual
example : state' = 0 := by
  rfl
-- ANCHOR_END: actual
"###;
        let example = extract_example(source, "actual").unwrap();
        assert!(example.contains("state' = 0"));
        assert!(extract_example(source, "decoy").is_err());
        assert!(extract_example(source, "identifier-decoy").is_err());
        assert!(mask("def text := r#\"unterminated\"").is_err());
        assert!(mask("def text := \"unterminated\\").is_err());
    }

    #[test]
    fn rejects_missing_and_malformed_example_anchors() {
        for (source, name, message) in [
            ("example : True := by trivial", "absent", "missing"),
            (
                "-- ANCHOR: a\nexample : True := by trivial",
                "a",
                "unterminated",
            ),
            ("-- ANCHOR_END: a", "a", "without a matching start"),
            (
                "-- ANCHOR: a\nexample : True := by trivial\n-- ANCHOR_END: b",
                "a",
                "mismatched",
            ),
            (
                "-- ANCHOR: a\n-- ANCHOR: b\n-- ANCHOR_END: b\n-- ANCHOR_END: a",
                "a",
                "nested",
            ),
            (
                "-- ANCHOR: a\nexample : True := by trivial\n-- ANCHOR_END: a\n-- ANCHOR: a\nexample : True := by trivial\n-- ANCHOR_END: a",
                "a",
                "duplicate",
            ),
            (
                "-- ANCHOR: a\nexample : True := by trivial\n-- ANCHOR_END: a\n-- ANCHOR: unclosed",
                "a",
                "unterminated",
            ),
            ("-- ANCHOR: invalid name", "a", "invalid"),
            ("-- ANCHOR: _leading", "a", "invalid"),
            ("-- ANCHOR: ünicode", "a", "invalid"),
            ("", "bad name", "invalid"),
            ("/- -- ANCHOR: a", "a", "unterminated Lean comment"),
        ] {
            let error = extract_example(source, name).unwrap_err().to_string();
            assert!(error.contains(message), "{source:?}: {error}");
        }
    }

    #[test]
    fn requires_one_complete_anonymous_example() {
        for (body, message) in [
            ("", "empty"),
            ("-- only a comment\n/- no proof -/", "empty"),
            ("def test := 0", "anonymous `example`"),
            ("  example : True := by trivial", "column-zero"),
            (
                "example : True := by trivial\nexample : True := by trivial",
                "exactly one",
            ),
            (
                "example : True := by trivial\ndef extra := 0",
                "exactly one",
            ),
            (
                "example : True := by trivial\n  example : True := by trivial",
                "exactly one",
            ),
            (
                "example : True := by trivial\n  def extra := 0",
                "exactly one",
            ),
            (
                "example : True := by trivial\n  private theorem extra : True := by trivial",
                "exactly one",
            ),
            ("example : True := by\ntrivial", "indented"),
            ("example : True", "example body"),
            ("example (n : Nat := 0) : n = n", "example body"),
            ("example : \"untrusted := text\" = \"text\"", "example body"),
        ] {
            let source = format!("-- ANCHOR: test\n{body}\n-- ANCHOR_END: test\n");
            let error = extract_example(&source, "test").unwrap_err().to_string();
            assert!(error.contains(message), "{body:?}: {error}");
        }
    }

    #[test]
    fn rejects_end_markers_that_cut_off_a_proof_continuation() {
        for suffix in ["  trivial", "\n-- proof continues\n/- more -/\n  trivial"] {
            let source =
                format!("-- ANCHOR: test\nexample : True := by\n-- ANCHOR_END: test\n{suffix}\n");
            let error = extract_example(&source, "test").unwrap_err().to_string();
            assert!(error.contains("ends before an indented continuation"));
        }
        let complete = "-- ANCHOR: test\nexample : True := by\n  trivial\n-- ANCHOR_END: test\n-- Next command\ndef next := 0\n";
        assert!(extract_example(complete, "test").is_ok());
    }

    #[test]
    fn selects_a_case_without_interpreting_its_binders() {
        let source = "inductive J : Nat → Prop where\n  -- | decoy : J 0\n  | first {n : Nat} (proof : Unknown n) :\n      J (match n with\n        | 0 => 0\n        | k => k)\n  | second : J 1\n";
        let first = extract_case(source, "first").unwrap();
        assert!(first.starts_with("inductive J : Nat → Prop where\n  | first"));
        assert!(first.contains("Unknown n"));
        assert!(first.contains("| k => k"));
        assert!(!first.contains("second"));
        assert!(extract_case(source, "decoy").is_err());
        assert!(!extract_case(
            "inductive J where\n  | r\n-- Next declaration documentation",
            "r"
        )
        .unwrap()
        .contains("documentation"));
        assert!(extract_case(source, "k").is_err());
        assert!(
            extract_case("inductive J : Prop where\n  | intro{n : Nat} : J", "intro")
                .unwrap()
                .contains("intro{n")
        );
        assert!(extract_case("inductive J where\n  | r\n  | r\n", "r").is_err());
    }
    #[test]
    fn extracts_complete_declarations_and_ignores_comment_decoys() {
        let s="/- inductive Place where\n /- nested -/ -/\ninductive Place where\n  | field (n : Nat)\n  | binding\n\ninductive Next where\n  | next\n";
        let d = extract(s, "Place").unwrap();
        assert!(d.contains("| binding"));
        assert!(!d.contains("Next"));
        assert!(extract("inductive X where\n  | x\ninductive X where\n  | y", "X").is_err());
        assert!(extract("-- inductive X where", "X").is_err());
        assert!(extract("def X := 1", "X").is_err());
        assert!(extract("inductive X where\n| x", "X").is_err());
        assert!(extract("@[expose]\ninductive X where\n  | x", "X").is_err());
    }
}

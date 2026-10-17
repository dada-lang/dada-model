//! Extraction of a deliberately restricted, line-oriented Lean declaration style.
use anyhow::{ensure, Context, Result};
use std::path::{Component, Path};

// Mask comments and strings while retaining byte offsets and newlines.
fn mask(source: &str) -> Result<String> {
    let bytes = source.as_bytes();
    let mut output = bytes.to_vec();
    let (mut i, mut depth, mut string, mut line) = (0, 0, false, false);
    while i < bytes.len() {
        let pair = bytes.get(i..i + 2);
        if line && bytes[i] == b'\n' {
            line = false;
        }
        if !string && !line && pair == Some(b"/-") {
            depth += 1;
            output[i] = b' ';
            output[i + 1] = b' ';
            i += 2;
            continue;
        }
        if depth > 0 && pair == Some(b"-/") {
            depth -= 1;
            output[i] = b' ';
            output[i + 1] = b' ';
            i += 2;
            continue;
        }
        if depth == 0 && !string && pair == Some(b"--") {
            line = true;
        }
        if depth == 0 && !line && bytes[i] == b'"' {
            string = !string;
            output[i] = b' ';
            i += 1;
            continue;
        }
        if string && bytes[i] == b'\\' {
            output[i] = b' ';
            if i + 1 < bytes.len() {
                output[i + 1] = b' ';
            }
            i += 2;
            continue;
        }
        if (depth > 0 || string || line) && bytes[i] != b'\n' {
            output[i] = b' ';
        }
        i += 1;
    }
    ensure!(depth == 0 && !string, "unterminated Lean comment or string");
    Ok(String::from_utf8(output)?)
}

pub fn extract(source: &str, name: &str) -> Result<String> {
    ensure!(
        !name.is_empty() && name.chars().all(|c| c.is_alphanumeric() || c == '_'),
        "use a simple unqualified declaration name"
    );
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
        if words.get(1) != Some(&name) {
            continue;
        }
        if !matches!(words.first(), Some(&"inductive" | &"structure" | &"abbrev")) {
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
            let word = boundary.split_whitespace().next().unwrap_or("");
            ensure!(
                matches!(
                    word,
                    "inductive"
                        | "structure"
                        | "abbrev"
                        | "def"
                        | "theorem"
                        | "lemma"
                        | "instance"
                        | "end"
                        | "namespace"
                        | "section"
                        | "variable"
                        | "open"
                        | "#check"
                ),
                "unsupported declaration boundary `{word}`; continuation lines must be indented"
            );
        }
        let end = lines[i + 1..]
            .iter()
            .find(|(_, l)| !l.trim().is_empty() && !l.starts_with(char::is_whitespace))
            .map(|(n, _)| *n)
            .unwrap_or(source.len());
        let text = source[start..end].trim_end();
        if words[0] != "abbrev" {
            ensure!(
                line.contains("where"),
                "declaration header must contain `where` on its first line"
            );
        } else {
            ensure!(line.contains(":="), "abbreviation header must contain `:=`");
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
    let keywords = regex::Regex::new(r"\b(inductive|structure|abbrev|where|deriving)\b")?;
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

fn selector(rendered: &str, source: &str, group: &str, label: &str) -> String {
    let group = crate::escape(group);
    format!("<figure class=\"lean-declaration lean-group\"><div class=\"lean-selector\" role=\"group\" aria-label=\"Declaration view\"><label><input type=\"radio\" name=\"{group}\" value=\"grammar\" checked> {label}</label><label><input type=\"radio\" name=\"{group}\" value=\"lean\"> Lean</label></div><div class=\"lean-grammar\">{rendered}</div><div class=\"lean-source\">{source}<p>Imports, namespaces and section variables remain in the source file.</p></div></figure>")
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
            view == View::Grammar || declaration.starts_with("inductive "),
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
    Ok(selector(&rendered, &source, group, "Rendered"))
}

#[cfg(test)]
mod tests {
    use super::*;
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

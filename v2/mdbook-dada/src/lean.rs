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

fn read_declaration(root: &Path, target: &str) -> Result<String> {
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
    let declaration = extract(&source, name).with_context(|| target.to_owned())?;
    Ok(declaration)
}

// A small display grammar for container applications, not a Lean elaborator.
// Balanced parenthesized arguments allow nested applications; all other text is escaped.
fn math_types(input: &str) -> String {
    fn atom_end(s: &str) -> Option<usize> {
        if s.starts_with('(') {
            let mut depth = 0;
            for (i, ch) in s.char_indices() {
                match ch {
                    '(' => depth += 1,
                    ')' => {
                        depth -= 1;
                        if depth == 0 {
                            return Some(i + 1);
                        }
                    }
                    _ => {}
                }
            }
            None
        } else {
            let end = s
                .find(|c: char| !(c.is_alphanumeric() || c == '_' || c == '.'))
                .unwrap_or(s.len());
            (end > 0).then_some(end)
        }
    }
    let mut out = String::new();
    let mut rest = input;
    while !rest.is_empty() {
        let mut matched = false;
        for (name, arity) in [("List", 1), ("Array", 1), ("FiniteMap", 2)] {
            let Some(tail) = rest.strip_prefix(name) else {
                continue;
            };
            if !tail.starts_with(char::is_whitespace) {
                continue;
            }
            let mut tail = tail;
            let mut args = Vec::new();
            for _ in 0..arity {
                if !tail.starts_with(char::is_whitespace) {
                    break;
                }
                tail = tail.trim_start();
                let Some(end) = atom_end(tail) else { break };
                args.push(math_types(&tail[..end]));
                tail = &tail[end..];
            }
            if args.len() != arity {
                continue;
            }
            if arity == 1 {
                out.push_str(&format!(
                    "<span class=\"math-sequence\" title=\"Finite ordered sequence\">{}</span>",
                    args[0]
                ));
            } else {
                out.push_str(&format!(
                    "<span class=\"math-map\">{} <span title=\"Finite map\">⇀</span> {}</span>",
                    args[0], args[1]
                ));
            }
            rest = tail;
            matched = true;
            break;
        }
        if matched {
            continue;
        }
        // Consume whole identifiers so a suffix like MyList is never rewritten.
        let end = atom_end(rest)
            .filter(|_| !rest.starts_with('('))
            .unwrap_or_else(|| rest.chars().next().unwrap().len_utf8());
        out.push_str(&crate::escape(&rest[..end]));
        rest = &rest[end..];
    }
    out
}

fn math_row(row: &str) -> String {
    match row.split_once(':') {
        Some((name, ty)) => format!("{}:{}", crate::escape(name), math_types(ty)),
        None => crate::escape(row),
    }
}

// Split only complete top-level constructor binders, preserving nested type syntax.
fn constructor_row(row: &str) -> String {
    let Some(start) = row.find('(') else {
        return math_row(row);
    };
    let mut rest = row[start..].trim();
    let mut fields = Vec::new();
    while !rest.is_empty() {
        if !rest.starts_with('(') {
            return math_row(row);
        }
        let mut depth = 0;
        let mut end = None;
        for (i, ch) in rest.char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        end = Some(i + 1);
                        break;
                    }
                }
                _ => {}
            }
        }
        let Some(end) = end else { return math_row(row) };
        if !rest[..end].contains(':') {
            return math_row(row);
        }
        fields.push(&rest[..end]);
        rest = rest[end..].trim();
    }
    if fields.len() < 2 {
        return math_row(row);
    }
    format!(
        "{}<span class=\"grammar-fields\">{}</span>",
        crate::escape(row[..start].trim()),
        fields
            .into_iter()
            .map(|f| format!("<span>{}</span>", math_row(f)))
            .collect::<String>()
    )
}

// Recognize only simple headers; bodies retain Lean identifiers and expressions.
fn compact(declaration: &str) -> Result<Option<String>> {
    let clean = mask(declaration)?;
    let header = clean.lines().next().unwrap_or("");
    let pattern =
        regex::Regex::new(r"^(inductive|structure) ([A-Za-z_][A-Za-z_0-9]*)(.*?) where\s*$")?;
    if let Some(c) = pattern.captures(header) {
        let params = c[3].trim();
        if !params.is_empty() && !(params.starts_with('(') && params.ends_with(')')) {
            return Ok(None);
        }
        let mut rows: Vec<String> = Vec::new();
        for line in clean
            .lines()
            .skip(1)
            .map(str::trim)
            .filter(|l| !l.is_empty())
        {
            if line.starts_with("deriving ") {
                continue;
            }
            if c[1] == *"structure" {
                if !line.contains(':') || line.contains(":=") {
                    return Ok(None);
                }
                rows.push(line.to_owned());
            } else if let Some(constructor) = line.strip_prefix('|') {
                rows.push(constructor.trim().to_owned());
            } else if let Some(last) = rows.last_mut() {
                // Wrapped constructor arguments remain part of the same alternative.
                if !line.starts_with('(') {
                    return Ok(None);
                }
                last.push(' ');
                last.push_str(line);
            } else {
                return Ok(None);
            }
        }
        if rows.is_empty() {
            return Ok(None);
        }
        let name = format!("{} {}", crate::escape(&c[2]), crate::escape(params));
        let mut cells = String::new();
        if c[1] == *"structure" {
            let rhs = rows
                .iter()
                .map(|r| math_row(r))
                .collect::<Vec<_>>()
                .join("; ");
            cells.push_str(&format!("<span class=\"grammar-name\">{name}</span><span class=\"grammar-marker\">:=</span><span class=\"grammar-rhs\">{rhs}</span>"));
        } else {
            for (i, row) in rows.iter().enumerate() {
                let lhs = if i == 0 { name.as_str() } else { "" };
                let marker = if i == 0 { ":=" } else { "|" };
                let rhs = constructor_row(row);
                cells.push_str(&format!("<span class=\"grammar-name\">{lhs}</span><span class=\"grammar-marker\">{marker}</span><span class=\"grammar-rhs\">{rhs}</span>"));
            }
        }
        return Ok(Some(format!(
            "<div class=\"grammar-definition\">{cells}</div>"
        )));
    }
    let alias =
        regex::Regex::new(r"^abbrev ([A-Za-z_][A-Za-z_0-9]*) := ([A-Za-z_][A-Za-z_0-9]*)\s*$")?;
    if let Some(c) = alias.captures(clean.trim()) {
        return Ok(Some(format!("<div class=\"grammar-definition\"><span class=\"grammar-name\">{}</span><span>:=</span><span class=\"grammar-rhs\">{} <small>(alias)</small></span></div>",crate::escape(&c[1]),crate::escape(&c[2]))));
    }
    Ok(None)
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

pub fn render_group(root: &Path, entries: &str, group: &str) -> Result<String> {
    let targets: Vec<_> = entries
        .lines()
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .collect();
    ensure!(
        !targets.is_empty(),
        "lean.type requires at least one file:Declaration entry"
    );
    let mut grammar = String::new();
    let mut source = String::new();
    for target in targets {
        let declaration = read_declaration(root, target)?;
        let lean = highlighted(&declaration)?;
        grammar.push_str(&match compact(&declaration)? {
            Some(html) => html,
            None => format!("<p>Compact notation unavailable for {}; showing Lean.</p><pre><code>{lean}</code></pre>",crate::escape(target)),
        });
        source.push_str(&format!(
            "<figcaption>{}</figcaption><pre><code class=\"language-lean\">{lean}</code></pre>",
            crate::escape(target)
        ));
    }
    let group = crate::escape(group);
    Ok(format!("<figure class=\"lean-declaration lean-group\"><div class=\"lean-selector\" role=\"group\" aria-label=\"Declaration view\"><label><input type=\"radio\" name=\"{group}\" value=\"grammar\" checked> Grammar</label><label><input type=\"radio\" name=\"{group}\" value=\"lean\"> Lean</label></div><div class=\"lean-grammar grammar-definitions\">{grammar}</div><div class=\"lean-source\">{source}<p>Imports, namespaces and section variables remain in the source file.</p></div></figure>"))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn alternatives_have_marker_cells_and_multiple_fields_are_indented() {
        let html = compact("inductive Place where\n  | binding (frame : FrameId) (name : BindingName)\n  | field (object : ObjectId) (name : FieldName)\n").unwrap().unwrap();
        assert!(html.contains("grammar-marker\">:=</span>"));
        assert!(html.contains("grammar-marker\">|</span>"));
        assert_eq!(html.matches("grammar-fields").count(), 2);
        assert!(!constructor_row("owned (object : ObjectId)").contains("grammar-fields"));
        let nested = constructor_row("state (objects : FiniteMap ObjectId (Object Primitive)) (frames : FiniteMap FrameId Frame)");
        assert!(nested.contains("(Object Primitive)"));
        assert_eq!(nested.matches("math-map").count(), 2);
        assert!(nested.contains("</span><span>(frames"));
    }

    #[test]
    fn mathematical_containers_preserve_arguments_and_unknown_text() {
        assert_eq!(math_types("List Slot"), math_types("Array Slot"));
        let nested = math_types("FiniteMap ObjectId (Object Primitive)");
        assert!(nested.contains("ObjectId"));
        assert!(nested.contains("⇀"));
        assert!(nested.contains("(Object Primitive)"));
        assert!(math_types("List (Key × Value)").contains("(Key × Value)</span>"));
        assert!(
            math_types("Array (List Slot)")
                .matches("math-sequence")
                .count()
                == 2
        );
        assert_eq!(math_types("MyList Slot"), "MyList Slot");
        assert_eq!(math_types("FiniteMap K"), "FiniteMap K");
        assert_eq!(math_types("<script>"), "&lt;script&gt;");
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

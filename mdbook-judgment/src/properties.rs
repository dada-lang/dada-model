//! Include property module documentation as Markdown, independently of snippets.

use std::path::Path;

use anyhow::{bail, ensure, Context, Result};

/// Directives occupy a standalone, unindented line. Fenced and indented code
/// stays literal, so chapters can demonstrate the directive syntax.
pub(crate) fn replace_properties(content: &str, root: &Path) -> Result<String> {
    let mut output = String::new();
    let mut fence: Option<(char, usize)> = None;
    for (line_index, line) in content.split_inclusive('\n').enumerate() {
        let trimmed = line.trim_start_matches(' ');
        let indent = line.len() - trimmed.len();
        let marker = trimmed.chars().next().unwrap_or('\n');
        let count = trimmed.chars().take_while(|&c| c == marker).count();
        if let Some((open_marker, open_count)) = fence {
            if indent <= 3
                && marker == open_marker
                && count >= open_count
                && trimmed[count..].trim().is_empty()
            {
                fence = None;
            }
            output.push_str(line);
            continue;
        }
        if indent <= 3
            && matches!(marker, '`' | '~')
            && count >= 3
            && (marker != '`' || !trimmed[count..].contains('`'))
        {
            fence = Some((marker, count));
            output.push_str(line);
            continue;
        }
        if !line.starts_with("{{property") {
            output.push_str(line);
            continue;
        }
        let directive = line.trim_end();
        let id = directive
            .strip_prefix("{{property ")
            .and_then(|s| s.strip_suffix("}}"))
            .map(str::trim)
            .with_context(|| {
                format!(
                    "line {}: expected {{{{property module::name}}}}",
                    line_index + 1
                )
            })?;
        output.push_str(
            &load_property(root, id)
                .with_context(|| format!("property `{id}` at line {}", line_index + 1))?,
        );
        output.push('\n');
    }
    Ok(output)
}

fn load_property(root: &Path, id: &str) -> Result<String> {
    ensure!(
        !id.is_empty()
            && id.split("::").all(|part| {
                let mut chars = part.chars();
                chars
                    .next()
                    .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                    && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
            }),
        "invalid property ID; use module names separated by `::`"
    );
    let base = root.join("src/properties").join(id.replace("::", "/"));
    let file = base.with_extension("rs");
    let directory = base.join("mod.rs");
    let path = match (file.is_file(), directory.is_file()) {
        (true, false) => file,
        (false, true) => directory,
        (false, false) => bail!(
            "missing property module: expected {} or {}",
            file.display(),
            directory.display()
        ),
        (true, true) => bail!(
            "ambiguous property module: both {} and {} exist",
            file.display(),
            directory.display()
        ),
    };
    let source =
        std::fs::read_to_string(&path).with_context(|| format!("reading {}", path.display()))?;
    let (docs, line) = module_docs(&source)
        .with_context(|| format!("{} needs a leading //! Markdown header", path.display()))?;
    let relative = path
        .strip_prefix(root)?
        .to_string_lossy()
        .replace('\\', "/");
    Ok(format!(
        "{docs}\n\n[Property source and tests]({})\n",
        crate::github_link(&relative, line)
    ))
}

fn module_docs(source: &str) -> Result<(String, usize)> {
    let mut lines = source.lines().enumerate().peekable();
    while lines.peek().is_some_and(|(_, line)| line.trim().is_empty()) {
        lines.next();
    }
    let first_line = lines.peek().map_or(1, |(i, _)| i + 1);
    let mut docs = Vec::new();
    for (_, line) in lines {
        let Some(doc) = line.trim_start().strip_prefix("//!") else {
            break;
        };
        docs.push(doc.strip_prefix(' ').unwrap_or(doc));
    }
    let docs = docs.join("\n");
    ensure!(
        !docs.trim().is_empty(),
        "missing or empty module documentation"
    );
    Ok((docs, first_line))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    struct Fixture(std::path::PathBuf);
    impl Fixture {
        fn new() -> Self {
            static NEXT: AtomicUsize = AtomicUsize::new(0);
            let path = std::env::temp_dir().join(format!(
                "dada-properties-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            std::fs::create_dir_all(&path).unwrap();
            Self(path)
        }
        fn write(&self, name: &str, content: &str) {
            let path = self.0.join("src/properties").join(name);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, content).unwrap();
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn includes_markdown_and_source_without_test_body() {
        let f = Fixture::new();
        f.write("moves.rs", "\n//! ## Moves\n//!\n//! **Claim** with `p`.\n//!\n//! - A list\n//!\n//! ```text\n//! p -> q\n//! ```\n\n#[test]\nfn hidden() {}\n");
        let result = replace_properties("Before\n\n{{property moves}}\n\nAfter\n", &f.0).unwrap();
        assert!(
            result.contains("## Moves\n\n**Claim** with `p`.\n\n- A list\n\n```text\np -> q\n```")
        );
        assert!(result.contains("src/properties/moves.rs#L2"));
        assert!(result.starts_with("Before\n\n"));
        assert!(result.ends_with("\nAfter\n"));
        assert!(!result.contains("hidden"));
    }

    #[test]
    fn resolves_file_directory_and_nested_modules() {
        let f = Fixture::new();
        f.write("a.rs", "//! File");
        f.write("b/mod.rs", "//! Directory");
        f.write("b/c.rs", "//! Nested file");
        f.write("b/d/mod.rs", "//! Nested directory");
        for (id, expected) in [
            ("a", "File"),
            ("b", "Directory"),
            ("b::c", "Nested file"),
            ("b::d", "Nested directory"),
        ] {
            assert!(load_property(&f.0, id).unwrap().starts_with(expected));
        }
    }

    #[test]
    fn code_examples_stay_literal() {
        let f = Fixture::new();
        let input = "```markdown\n{{property missing}}\n```\n\n~~~~\n{{property missing}}\n~~~\n{{property still_missing}}\n~~~~\n\n    {{property missing}}\n\t{{property missing}}\n\n`{{property missing}}`\n";
        assert_eq!(replace_properties(input, &f.0).unwrap(), input);
        f.write("real.rs", "//! Real");
        assert!(
            replace_properties(&format!("{input}\n{{{{property real}}}}"), &f.0)
                .unwrap()
                .ends_with("#L1)\n\n")
        );
    }

    #[test]
    fn errors_identify_missing_ambiguous_and_undocumented_properties() {
        let f = Fixture::new();
        assert!(format!(
            "{:#}",
            replace_properties("{{property absent}}", &f.0).unwrap_err()
        )
        .contains("missing property module"));
        f.write("a.rs", "//! A");
        f.write("a/mod.rs", "//! Also A");
        assert!(load_property(&f.0, "a")
            .unwrap_err()
            .to_string()
            .contains("ambiguous"));
        for body in [
            "fn test() {}",
            "//!\nfn test() {}",
            "fn test() {}\n//! Not a header",
        ] {
            f.write("empty.rs", body);
            assert!(load_property(&f.0, "empty")
                .unwrap_err()
                .to_string()
                .contains("leading //!"));
        }
        for id in ["", "../escape", "a::", "a/b", "0name"] {
            assert!(load_property(&f.0, id)
                .unwrap_err()
                .to_string()
                .contains("invalid property ID"));
        }
        assert!(replace_properties("{{property a}", &f.0).is_err());
    }
}

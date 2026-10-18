use anyhow::{Context, Result};
use mdbook_dada::{lint::check_latex, process};
use serde_json::json;
use std::{fs, path::Path};

#[test]
fn overbars_require_a_preceding_brace_and_following_literal_space() {
    for source in [
        r"\overline f,x",
        r"{ \overline f}",
        r"\overline{f}",
        r"{\overline{f}}",
        "{\\overline\tf}",
        "{\\overline\nf}",
        "{\\overline\r\nf}",
        "{\\overline\u{a0}f}",
        r"\overline {f}",
        r"{\overline7}",
        r"{\overline\alpha}",
        r"{\overline}",
        r"{\overline",
        r"\overline",
    ] {
        let error = check_latex(source, "state.md").unwrap_err().to_string();
        assert!(error.contains("state.md:1:"), "{source:?}: {error}");
        assert!(error.contains(r"use {\overline f}"), "{error}");
    }
}

#[test]
fn grouped_overbars_and_other_control_words_are_allowed() {
    for source in [
        r"{\overline f},x",
        r"{\overline {f_1, f_2}}",
        r"{\overline {\overline f}}",
        r"{\overline \alpha}",
        r"{\overline f} + {\overline g}",
        r"\overlineSomething f",
        r"\overlined f",
        "No math here.",
    ] {
        check_latex(source, "state.md").unwrap();
    }
}

#[test]
fn diagnostics_count_source_lines_including_unicode_and_crlf() {
    let source = "# α\r\n{\\overline f}\r\n\r\n\\overline f";
    let error = check_latex(source, "nested/chapter.md")
        .unwrap_err()
        .to_string();
    assert!(error.starts_with("nested/chapter.md:4:"), "{error}");
}

#[test]
fn book_build_checks_math_directives_examples_and_literal_tex() {
    for source in [
        r"Inline \\(\overline f\\).",
        "```{grammar} Heap.lean:Object\n\\overline f\n```",
        "````{example} Heap.lean:integer_primitive\n\\overline f\n````",
        "```latex\n\\overline f\n```",
    ] {
        let mut book = json!({"items": [{"Chapter": {
            "path": "intro.md", "content": "Introduction.", "sub_items": [
                {"Chapter": {"path": "nested/state.md", "content": source, "sub_items": []}}
            ]
        }}]});
        let error = process(&mut book).unwrap_err().to_string();
        assert!(error.contains("nested/state.md:"), "{error}");
        assert!(error.contains(r"use {\overline f}"), "{error}");
    }
}

// meta.math.overline.braces: include unlisted chapters and literal TeX samples.
#[test]
fn all_book_markdown_follows_latex_conventions() -> Result<()> {
    fn scan(directory: &Path, errors: &mut Vec<String>, count: &mut usize) -> Result<()> {
        let mut entries = fs::read_dir(directory)
            .with_context(|| format!("read {}", directory.display()))?
            .collect::<std::io::Result<Vec<_>>>()?;
        entries.sort_by_key(|entry| entry.path());
        for entry in entries {
            let path = entry.path();
            if entry.file_type()?.is_dir() {
                scan(&path, errors, count)?;
            } else if path.extension().is_some_and(|extension| extension == "md") {
                *count += 1;
                let source = fs::read_to_string(&path)
                    .with_context(|| format!("read {}", path.display()))?;
                if let Err(error) = check_latex(&source, &path.display().to_string()) {
                    errors.push(error.to_string());
                }
            }
        }
        Ok(())
    }

    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../md");
    let mut errors = Vec::new();
    let mut count = 0;
    scan(&root, &mut errors, &mut count)?;
    assert!(count > 0, "no book Markdown found under {}", root.display());
    assert!(errors.is_empty(), "{}", errors.join("\n"));
    Ok(())
}

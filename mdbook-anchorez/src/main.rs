use std::collections::HashMap;
use std::io;
use std::path::{Path, PathBuf};
use std::process;

use mdbook_preprocessor::book::{Book, BookItem};
use mdbook_preprocessor::{Preprocessor, PreprocessorContext};
use regex::Regex;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() > 1 && args[1] == "supports" {
        // We support all renderers
        process::exit(0);
    }

    let (ctx, book) = mdbook_preprocessor::parse_input(io::stdin()).expect("failed to parse mdbook input from stdin");
    let preprocessor = AnchorezPreprocessor;
    let processed = preprocessor
        .run(&ctx, book)
        .expect("failed to run anchorez preprocessor");
    serde_json::to_writer(io::stdout(), &processed).expect("failed to write processed book to stdout");
}

struct AnchorezPreprocessor;

impl Preprocessor for AnchorezPreprocessor {
    fn name(&self) -> &str {
        "anchorez"
    }

    fn run(&self, ctx: &PreprocessorContext, mut book: Book) -> anyhow::Result<Book> {
        let root = ctx.root.clone();

        // Read optional config from [preprocessor.anchorez] in book.toml
        let src_dir_name = ctx
            .config
            .get::<String>("preprocessor.anchorez.src-dir")
            .ok()
            .flatten()
            .unwrap_or_else(|| "src".to_string());

        let github_base = ctx
            .config
            .get::<String>("preprocessor.anchorez.github-base")
            .ok()
            .flatten()
            .unwrap_or_default();

        let src_dir = root.join(&src_dir_name);
        let anchors = scan_anchors(&src_dir, &root)?;

        book.for_each_mut(|item| {
            if let BookItem::Chapter(chapter) = item {
                chapter.content = replace_anchor_refs(&chapter.content, &anchors, &github_base);
            }
        });

        Ok(book)
    }

    fn supports_renderer(&self, _renderer: &str) -> anyhow::Result<bool> {
        Ok(true)
    }
}

// --- Data structures ---

#[derive(Debug)]
struct Anchor {
    name: String,
    content: String,
    /// Path relative to project root, e.g. "src/grammar.rs"
    file_path: String,
    /// 1-based line number of the `// ANCHOR: name` line
    line_number: usize,
}

// --- Source scanning ---

fn scan_anchors(src_dir: &Path, root: &Path) -> anyhow::Result<HashMap<String, Anchor>> {
    let mut anchors = HashMap::new();

    for entry in walk_rs_files(src_dir)? {
        let content = std::fs::read_to_string(&entry)?;
        let rel_path = entry
            .strip_prefix(root)
            .unwrap_or(&entry)
            .to_string_lossy()
            .to_string();
        for anchor in parse_anchors(&content, &rel_path) {
            anchors.insert(anchor.name.clone(), anchor);
        }
    }

    Ok(anchors)
}

fn walk_rs_files(dir: &Path) -> anyhow::Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    if !dir.exists() {
        return Ok(files);
    }
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            files.extend(walk_rs_files(&path)?);
        } else if path.extension().map_or(false, |e| e == "rs") {
            files.push(path);
        }
    }
    Ok(files)
}

// --- Anchor parsing ---

fn parse_anchors(content: &str, file_path: &str) -> Vec<Anchor> {
    let mut anchors = Vec::new();
    let anchor_start_re = Regex::new(r"// ANCHOR: (\w+)").unwrap();

    for mat in anchor_start_re.find_iter(content) {
        let caps = anchor_start_re.captures(&content[mat.start()..]).unwrap();
        let name = caps.get(1).unwrap().as_str().to_string();
        let line_number = content[..mat.start()].matches('\n').count() + 1;

        let end_marker = format!("// ANCHOR_END: {name}");
        let after_start = mat.end();
        if let Some(end_offset) = content[after_start..].find(&end_marker) {
            let anchor_content = content[after_start..after_start + end_offset]
                .trim_start_matches('\n')
                .trim_end_matches('\n')
                .to_string();

            anchors.push(Anchor {
                name,
                content: dedent(&anchor_content),
                file_path: file_path.to_string(),
                line_number,
            });
        }
    }

    anchors
}

fn dedent(text: &str) -> String {
    let lines: Vec<&str> = text.lines().collect();
    let min_indent = lines
        .iter()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.len() - l.trim_start().len())
        .min()
        .unwrap_or(0);

    lines
        .iter()
        .map(|l| {
            if l.len() >= min_indent {
                &l[min_indent..]
            } else {
                l.trim()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

// --- Rendering ---

/// Render a `<figure>` element with a code block and an optional `[src]` link.
fn render_figure(css_class: &str, id: &str, label: &str, src_link: &str, code: &str) -> String {
    let src_link_html = if !src_link.is_empty() {
        format!(
            "<a class=\"judgment-src\" href=\"{src_link}\" title=\"View source\" target=\"_blank\">[src]</a>\n"
        )
    } else {
        String::new()
    };

    format!(
        "<figure class=\"{css_class}\" id=\"{id}\">\n\
         <figcaption>\n\
         <a href=\"#{id}\">{label}</a>\n\
         {src_link_html}\
         </figcaption>\n\
         \n\
         ```rust,ignore\n\
         {code}\n\
         ```\n\
         \n\
         </figure>\n",
    )
}

fn github_link(github_base: &str, file_path: &str, line: usize) -> String {
    if github_base.is_empty() {
        String::new()
    } else {
        format!("{github_base}/{file_path}#L{line}")
    }
}

fn render_anchor(anchor: &Anchor, github_base: &str) -> String {
    let link = github_link(github_base, &anchor.file_path, anchor.line_number);
    let id = format!("anchor-{}", anchor.name);
    render_figure("anchor", &id, &anchor.name, &link, &anchor.content)
}

// --- Markdown replacement ---

fn replace_anchor_refs(
    content: &str,
    anchors: &HashMap<String, Anchor>,
    github_base: &str,
) -> String {
    let anchor_re = Regex::new(r#"\{anchor\}`(\w+)`"#).unwrap();
    anchor_re
        .replace_all(content, |caps: &regex::Captures| {
            let anchor_name = &caps[1];

            match anchors.get(anchor_name) {
                Some(anchor) => render_anchor(anchor, github_base),
                None => {
                    eprintln!("warning: anchor `{anchor_name}` not found");
                    format!("**[anchor `{anchor_name}` not found]**")
                }
            }
        })
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    const ANCHOR_SAMPLE: &str = r#"
some preamble
// ANCHOR: Env
pub struct Env {
    program: Arc<Program>,
    local_variables: Map<Var, Ty>,
}
// ANCHOR_END: Env
some postamble
"#;

    fn make_anchors() -> HashMap<String, Anchor> {
        let anchors = parse_anchors(ANCHOR_SAMPLE, "src/type_system/env.rs");
        let mut anchor_map = HashMap::new();
        for a in anchors {
            anchor_map.insert(a.name.clone(), a);
        }
        anchor_map
    }

    #[test]
    fn test_parse_anchors() {
        let anchors = parse_anchors(ANCHOR_SAMPLE, "src/type_system/env.rs");
        assert_eq!(anchors.len(), 1);
        let a = &anchors[0];
        assert_eq!(a.name, "Env");
        assert!(a.content.contains("pub struct Env"), "content: {}", a.content);
        assert!(a.content.contains("local_variables"), "content: {}", a.content);
        assert_eq!(a.file_path, "src/type_system/env.rs");
        assert_eq!(a.line_number, 3);
    }

    #[test]
    fn test_anchor_replacement_with_github_base() {
        let anchors = make_anchors();
        let github_base = "https://github.com/dada-lang/dada-model/blob/main";
        let input = "The env: {anchor}`Env`";
        let output = replace_anchor_refs(input, &anchors, github_base);
        assert!(output.contains("pub struct Env"), "output: {output}");
        assert!(output.contains("github.com"), "output: {output}");
        assert!(output.contains("anchor-Env"), "output: {output}");
        assert!(output.contains("[src]"), "output: {output}");
        assert!(!output.contains("{anchor}"), "output: {output}");
    }

    #[test]
    fn test_anchor_replacement_without_github_base() {
        let anchors = make_anchors();
        let input = "The env: {anchor}`Env`";
        let output = replace_anchor_refs(input, &anchors, "");
        assert!(output.contains("pub struct Env"), "output: {output}");
        assert!(output.contains("anchor-Env"), "output: {output}");
        assert!(!output.contains("[src]"), "output: {output}");
        assert!(!output.contains("{anchor}"), "output: {output}");
    }

    #[test]
    fn test_anchor_not_found() {
        let anchors = make_anchors();
        let input = "{anchor}`nonexistent`";
        let output = replace_anchor_refs(input, &anchors, "");
        assert!(output.contains("not found"), "output: {output}");
    }

    #[test]
    fn test_dedent() {
        let input = "    line1\n    line2\n        line3";
        let output = dedent(input);
        assert_eq!(output, "line1\nline2\n    line3");
    }
}

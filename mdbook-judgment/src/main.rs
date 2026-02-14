use std::collections::HashMap;
use std::io;
use std::path::{Path, PathBuf};
use std::process;

use mdbook_preprocessor::book::{Book, BookItem};
use mdbook_preprocessor::{Preprocessor, PreprocessorContext};
use regex::Regex;

const GITHUB_BASE: &str = "https://github.com/dada-lang/dada-model/blob/main";

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() > 1 && args[1] == "supports" {
        // We support all renderers
        process::exit(0);
    }

    let (ctx, book) = mdbook_preprocessor::parse_input(io::stdin()).expect("failed to parse input");
    let preprocessor = JudgmentPreprocessor;
    let processed = preprocessor
        .run(&ctx, book)
        .expect("failed to run preprocessor");
    serde_json::to_writer(io::stdout(), &processed).expect("failed to write output");
}

struct JudgmentPreprocessor;

impl Preprocessor for JudgmentPreprocessor {
    fn name(&self) -> &str {
        "judgment"
    }

    fn run(&self, ctx: &PreprocessorContext, mut book: Book) -> anyhow::Result<Book> {
        let root = ctx.root.clone();
        let src_dir = root.join("src");
        let index = scan_source_files(&src_dir, &root)?;

        book.for_each_mut(|item| {
            if let BookItem::Chapter(chapter) = item {
                chapter.content = replace_refs(&chapter.content, &index);
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
struct SourceIndex {
    judgments: HashMap<String, Judgment>,
    anchors: HashMap<String, Anchor>,
}

#[derive(Debug)]
struct Anchor {
    name: String,
    content: String,
    /// Path relative to project root, e.g. "src/grammar.rs"
    file_path: String,
    /// 1-based line number of the `// ANCHOR: name` line
    line_number: usize,
}

#[derive(Debug)]
struct Judgment {
    name: String,
    doc_comment: String,
    signature: String,
    /// Path relative to project root, e.g. "src/type_system/expressions.rs"
    file_path: String,
    /// 1-based line number of the judgment_fn! invocation
    line_number: usize,
    rules: Vec<Rule>,
}

#[derive(Debug)]
struct Rule {
    name: String,
    raw_text: String,
    /// 1-based line number of the separator line (the `---+ ("name")` line)
    line_number: usize,
}

// --- Source scanning ---

fn scan_source_files(src_dir: &Path, root: &Path) -> anyhow::Result<SourceIndex> {
    let mut judgments = HashMap::new();
    let mut anchors = HashMap::new();

    for entry in walk_rs_files(src_dir)? {
        let content = std::fs::read_to_string(&entry)?;
        let rel_path = entry
            .strip_prefix(root)
            .unwrap_or(&entry)
            .to_string_lossy()
            .to_string();
        for judgment in parse_judgment_fns(&content, &rel_path) {
            judgments.insert(judgment.name.clone(), judgment);
        }
        for anchor in parse_anchors(&content, &rel_path) {
            anchors.insert(anchor.name.clone(), anchor);
        }
    }

    Ok(SourceIndex { judgments, anchors })
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

// --- Judgment parsing ---

fn parse_judgment_fns(content: &str, file_path: &str) -> Vec<Judgment> {
    let mut judgments = Vec::new();
    let mut pos = 0;

    while let Some(start) = content[pos..].find("judgment_fn!") {
        let abs_start = pos + start;

        // Compute 1-based line number for the judgment_fn! invocation
        let jf_line = content[..abs_start].matches('\n').count() + 1;

        // Find the opening brace
        let Some(brace_start) = content[abs_start..].find('{') else {
            pos = abs_start + 12;
            continue;
        };
        let brace_start = abs_start + brace_start;

        // Find the matching closing brace
        let Some(brace_end) = find_matching_brace(content, brace_start) else {
            pos = brace_start + 1;
            continue;
        };

        let block = &content[brace_start + 1..brace_end];
        // Line number offset: lines before brace_start + 1
        let block_start_line = content[..brace_start + 1].matches('\n').count() + 1;

        if let Some(judgment) =
            parse_single_judgment(block, &content[..abs_start], file_path, jf_line, block_start_line)
        {
            judgments.push(judgment);
        }

        pos = brace_end + 1;
    }

    judgments
}

fn find_matching_brace(content: &str, open_pos: usize) -> Option<usize> {
    let mut depth = 0;
    let mut in_string = false;
    let mut in_line_comment = false;
    let mut prev_char = '\0';

    for (i, ch) in content[open_pos..].char_indices() {
        if in_line_comment {
            if ch == '\n' {
                in_line_comment = false;
            }
            prev_char = ch;
            continue;
        }

        if in_string {
            if ch == '"' && prev_char != '\\' {
                in_string = false;
            }
            prev_char = ch;
            continue;
        }

        if ch == '/' && prev_char == '/' {
            in_line_comment = true;
            prev_char = ch;
            continue;
        }

        if ch == '"' {
            in_string = true;
            prev_char = ch;
            continue;
        }

        if ch == '{' {
            depth += 1;
        } else if ch == '}' {
            depth -= 1;
            if depth == 0 {
                return Some(open_pos + i);
            }
        }

        prev_char = ch;
    }

    None
}

fn parse_single_judgment(
    block: &str,
    preceding: &str,
    file_path: &str,
    jf_line: usize,
    block_start_line: usize,
) -> Option<Judgment> {
    let doc_comment = extract_doc_comment(preceding);

    let fn_re = Regex::new(r"(?s)(pub\s+)?fn\s+(\w+)\s*\((.*?)\)\s*=>\s*([^{]+)\{").unwrap();
    let captures = fn_re.captures(block)?;

    let name = captures.get(2)?.as_str().to_string();
    let params = captures.get(3)?.as_str();
    let return_ty = captures.get(4)?.as_str().trim();

    let clean_params = clean_params(params);
    let signature = format!("{name}({clean_params}) => {return_ty}");

    let rules = extract_rules(block, block_start_line);

    Some(Judgment {
        name,
        doc_comment,
        signature,
        file_path: file_path.to_string(),
        line_number: jf_line,
        rules,
    })
}

fn extract_doc_comment(preceding: &str) -> String {
    let lines: Vec<&str> = preceding.lines().collect();
    let mut doc_lines = Vec::new();

    for line in lines.iter().rev() {
        let trimmed = line.trim();
        if trimmed.starts_with("///") {
            doc_lines.push(trimmed.trim_start_matches("///").trim());
        } else if trimmed.is_empty() {
            continue;
        } else {
            break;
        }
    }

    doc_lines.reverse();
    doc_lines.join("\n")
}

fn clean_params(params: &str) -> String {
    params
        .lines()
        .map(|l| l.trim())
        .filter(|l| !l.is_empty())
        .collect::<Vec<_>>()
        .join(" ")
        .replace(" ,", ",")
}

fn extract_rules(block: &str, block_start_line: usize) -> Vec<Rule> {
    let mut rules = Vec::new();

    // Find the position after `debug(...)` — skip past the closing paren
    let after_debug_offset = if let Some(debug_start) = block.find("debug(") {
        let paren_close =
            find_matching_paren(block, debug_start + 5).unwrap_or(debug_start + 6);
        paren_close + 1
    } else {
        0
    };

    let after_debug = &block[after_debug_offset..];
    // Line offset of after_debug relative to the block start
    let after_debug_line_offset = block[..after_debug_offset].matches('\n').count();

    let mut pos = 0;
    while pos < after_debug.len() {
        let trimmed_start = after_debug[pos..].find(|c: char| !c.is_whitespace());
        let Some(trimmed_offset) = trimmed_start else {
            break;
        };
        pos += trimmed_offset;

        if !after_debug[pos..].starts_with('(') {
            if let Some(nl) = after_debug[pos..].find('\n') {
                pos += nl + 1;
            } else {
                break;
            }
            continue;
        }

        let Some(close) = find_matching_paren(after_debug, pos) else {
            pos += 1;
            continue;
        };

        let rule_text = &after_debug[pos + 1..close];

        if let Some(rule_name) = extract_rule_name(rule_text) {
            // Find the separator line within rule_text to compute its line number
            let separator_re = Regex::new(r#"-{3,}\s*\("[^"]+"\)"#).unwrap();
            let separator_line_offset = if let Some(m) = separator_re.find(rule_text) {
                rule_text[..m.start()].matches('\n').count()
            } else {
                0
            };

            // Line number: block_start_line + lines to after_debug + lines to rule start + separator offset
            let rule_start_lines = after_debug[..pos + 1].matches('\n').count();
            let abs_line = block_start_line
                + after_debug_line_offset
                + rule_start_lines
                + separator_line_offset;

            rules.push(Rule {
                name: rule_name,
                raw_text: clean_rule_text(rule_text),
                line_number: abs_line,
            });
        }

        pos = close + 1;
    }

    rules
}

fn find_matching_paren(text: &str, open_pos: usize) -> Option<usize> {
    let mut depth = 0;
    let mut in_string = false;
    let mut in_line_comment = false;
    let mut prev_char = '\0';

    for (i, ch) in text[open_pos..].char_indices() {
        if in_line_comment {
            if ch == '\n' {
                in_line_comment = false;
            }
            prev_char = ch;
            continue;
        }

        if in_string {
            if ch == '"' && prev_char != '\\' {
                in_string = false;
            }
            prev_char = ch;
            continue;
        }

        if ch == '/' && prev_char == '/' {
            in_line_comment = true;
            prev_char = ch;
            continue;
        }

        if ch == '"' {
            in_string = true;
            prev_char = ch;
            continue;
        }

        if ch == '(' {
            depth += 1;
        } else if ch == ')' {
            depth -= 1;
            if depth == 0 {
                return Some(open_pos + i);
            }
        }

        prev_char = ch;
    }

    None
}

fn extract_rule_name(rule_text: &str) -> Option<String> {
    let re = Regex::new(r#"-{3,}\s*\("([^"]+)"\)"#).unwrap();
    let captures = re.captures(rule_text)?;
    Some(captures.get(1)?.as_str().to_string())
}

fn clean_rule_text(rule_text: &str) -> String {
    let lines: Vec<&str> = rule_text.lines().collect();

    let min_indent = lines
        .iter()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.len() - l.trim_start().len())
        .min()
        .unwrap_or(0);

    lines
        .iter()
        .map(|l| {
            if l.trim().is_empty() {
                ""
            } else if l.len() >= min_indent {
                &l[min_indent..]
            } else {
                l.trim()
            }
        })
        .filter(|l| !l.trim_start().starts_with("//"))
        .collect::<Vec<_>>()
        .join("\n")
        .trim()
        .to_string()
}

// --- Rendering ---

/// Render a `<figure>` element with a code block and `[src]` link.
/// This is the common rendering for judgments, judgment rules, and anchors.
fn render_figure(
    css_class: &str,
    id: &str,
    label: &str,
    src_link: &str,
    code: &str,
    doc: Option<&str>,
) -> String {
    let mut out = format!(
        "<figure class=\"{css_class}\" id=\"{id}\">\n\
         <figcaption>\n\
         <a href=\"#{id}\">{label}</a>\n\
         <a class=\"judgment-src\" href=\"{src_link}\" title=\"View source\" target=\"_blank\">[src]</a>\n\
         </figcaption>\n\
         \n\
         ```rust,ignore\n\
         {code}\n\
         ```\n",
    );

    if let Some(doc) = doc {
        out.push('\n');
        out.push_str(doc);
        out.push('\n');
    }

    out.push_str("\n</figure>\n");
    out
}

fn github_link(file_path: &str, line: usize) -> String {
    format!("{GITHUB_BASE}/{file_path}#L{line}")
}

fn render_rule(judgment: &Judgment, rule_name: &str) -> String {
    match judgment.rules.iter().find(|r| r.name == rule_name) {
        Some(rule) => {
            let link = github_link(&judgment.file_path, rule.line_number);
            let id = format!("judgment-{}--{}", judgment.name, rule_name);
            let label = format!("{}::{}", judgment.name, rule_name);
            render_figure("judgment-rule", &id, &label, &link, &rule.raw_text, None)
        }
        None => {
            eprintln!(
                "warning: rule `{}` not found in judgment `{}`",
                rule_name, judgment.name
            );
            format!(
                "**[rule `{}` not found in `{}`]**",
                rule_name, judgment.name
            )
        }
    }
}

fn render_judgment(judgment: &Judgment) -> String {
    let link = github_link(&judgment.file_path, judgment.line_number);
    let id = format!("judgment-{}", judgment.name);
    let doc = if judgment.doc_comment.is_empty() {
        None
    } else {
        Some(judgment.doc_comment.as_str())
    };
    render_figure("judgment", &id, &judgment.name, &link, &judgment.signature, doc)
}

fn render_anchor(anchor: &Anchor) -> String {
    let link = github_link(&anchor.file_path, anchor.line_number);
    let id = format!("anchor-{}", anchor.name);
    render_figure("anchor", &id, &anchor.name, &link, &anchor.content, None)
}

// --- Markdown replacement ---

fn replace_refs(content: &str, index: &SourceIndex) -> String {
    // First pass: {judgment-rule}`fn_name, rule_name`
    let rule_re = Regex::new(r#"\{judgment-rule\}`(\w+),\s*(\w[\w\s\-|]*\w|\w+)`"#).unwrap();
    let content = rule_re.replace_all(content, |caps: &regex::Captures| {
        let fn_name = &caps[1];
        let rule_name = caps[2].trim();

        match index.judgments.get(fn_name) {
            Some(judgment) => render_rule(judgment, rule_name),
            None => {
                eprintln!("warning: judgment function `{fn_name}` not found");
                format!("**[judgment `{fn_name}` not found]**")
            }
        }
    });

    // Second pass: {judgment}`fn_name`
    let judgment_re = Regex::new(r#"\{judgment\}`(\w+)`"#).unwrap();
    let content = judgment_re
        .replace_all(&content, |caps: &regex::Captures| {
            let fn_name = &caps[1];

            match index.judgments.get(fn_name) {
                Some(judgment) => render_judgment(judgment),
                None => {
                    eprintln!("warning: judgment function `{fn_name}` not found");
                    format!("**[judgment `{fn_name}` not found]**")
                }
            }
        })
        .to_string();

    // Third pass: {anchor}`anchor_name`
    let anchor_re = Regex::new(r#"\{anchor\}`(\w+)`"#).unwrap();
    anchor_re
        .replace_all(&content, |caps: &regex::Captures| {
            let anchor_name = &caps[1];

            match index.anchors.get(anchor_name) {
                Some(anchor) => render_anchor(anchor),
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

    const SAMPLE: &str = r#"
judgment_fn! {
    /// Compute the move/copy behavior for a place access.
    fn move_place(
        env: Env,
        live_after: LivePlaces,
        place: Place,
        ty: Ty,
    ) => Env {
        debug(place, ty, env, live_after)

        (
            (if live_after.is_live(&place))!
            (prove_is_copy(&env, ty) => ())
            ----------------------------------- ("copy")
            (move_place(env, _live_after, _place, ty) => &env)
        )

        (
            (if !live_after.is_live(&place))
            (let env = env.with_place_in_flight(&place))
            ----------------------------------- ("give")
            (move_place(env, live_after, place, _ty) => env)
        )
    }
}
"#;

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

    fn make_index() -> SourceIndex {
        let judgments = parse_judgment_fns(SAMPLE, "src/type_system/expressions.rs");
        let mut judgment_map = HashMap::new();
        for j in judgments {
            judgment_map.insert(j.name.clone(), j);
        }

        let anchors = parse_anchors(ANCHOR_SAMPLE, "src/type_system/env.rs");
        let mut anchor_map = HashMap::new();
        for a in anchors {
            anchor_map.insert(a.name.clone(), a);
        }

        SourceIndex {
            judgments: judgment_map,
            anchors: anchor_map,
        }
    }

    #[test]
    fn test_parse_judgment() {
        let judgments = parse_judgment_fns(SAMPLE, "src/type_system/expressions.rs");
        assert_eq!(judgments.len(), 1);
        let j = &judgments[0];
        assert_eq!(j.name, "move_place");
        assert_eq!(j.rules.len(), 2);
        assert_eq!(j.rules[0].name, "copy");
        assert_eq!(j.rules[1].name, "give");
        assert_eq!(j.file_path, "src/type_system/expressions.rs");
    }

    #[test]
    fn test_extract_rule_name() {
        assert_eq!(
            extract_rule_name(r#"  --- ("foo")  "#),
            Some("foo".to_string())
        );
        assert_eq!(
            extract_rule_name(r#"  ----------------------------------- ("share-share")  "#),
            Some("share-share".to_string())
        );
    }

    #[test]
    fn test_judgment_shows_signature_only() {
        let index = make_index();
        let input = "The judgment: {judgment}`move_place`";
        let output = replace_refs(input, &index);
        assert!(output.contains("move_place("), "output: {output}");
        assert!(output.contains("judgment-src"), "output: {output}");
        // Should NOT contain individual rule text
        assert!(!output.contains("prove_is_copy"), "output: {output}");
    }

    #[test]
    fn test_judgment_rule_shows_rule_with_link() {
        let index = make_index();
        let input = r#"The copy rule: {judgment-rule}`move_place, copy`"#;
        let output = replace_refs(input, &index);
        assert!(output.contains("prove_is_copy"), "output: {output}");
        assert!(output.contains("github.com"), "output: {output}");
        assert!(
            output.contains("move_place::copy"),
            "output: {output}"
        );
    }

    #[test]
    fn test_both_in_same_content() {
        let index = make_index();
        let input = r#"Sig: {judgment}`move_place`

Rule: {judgment-rule}`move_place, copy`"#;
        let output = replace_refs(input, &index);
        assert!(output.contains("move_place("), "output: {output}");
        assert!(output.contains("prove_is_copy"), "output: {output}");
        assert!(!output.contains("{judgment"), "output: {output}");
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
    fn test_anchor_replacement() {
        let index = make_index();
        let input = "The env: {anchor}`Env`";
        let output = replace_refs(input, &index);
        assert!(output.contains("pub struct Env"), "output: {output}");
        assert!(output.contains("github.com"), "output: {output}");
        assert!(output.contains("anchor-Env"), "output: {output}");
        assert!(output.contains("[src]"), "output: {output}");
        assert!(!output.contains("{anchor}"), "output: {output}");
    }
}

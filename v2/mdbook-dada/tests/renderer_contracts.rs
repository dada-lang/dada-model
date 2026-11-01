//! Checks of the shipped presentation configuration and diagram fact boundaries.
//! Asset checks inspect local configuration; they do not execute a browser or CDN.
use mdbook_dada::{graph, process};
use serde_json::json;
use std::{fs, path::PathBuf};

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .to_owned()
}

fn read_asset(path: &str) -> String {
    fs::read_to_string(project_root().join(path)).unwrap()
}

#[test]
fn pinned_mathjax_configuration_uses_one_loader() {
    let config: toml::Value = toml::from_str(&read_asset("book.toml")).unwrap();
    let html = &config["output"]["html"];
    assert_eq!(html["mathjax-support"].as_bool(), Some(false));
    let scripts = html["additional-js"].as_array().unwrap();
    assert_eq!(
        scripts.len(),
        1,
        "review any added loader for duplicate MathJax initialization"
    );
    assert_eq!(scripts[0].as_str(), Some("theme/mathjax.js"));
    assert!(html["additional-css"]
        .as_array()
        .unwrap()
        .iter()
        .any(|path| path.as_str() == Some("theme/dada.css")));

    let script = read_asset("theme/mathjax.js");
    let urls = regex::Regex::new(r#"https://[^'"\s]+"#).unwrap();
    let urls: Vec<_> = urls.find_iter(&script).map(|m| m.as_str()).collect();
    assert_eq!(
        urls,
        ["https://cdn.jsdelivr.net/npm/mathjax@4.1.3/tex-chtml.js"]
    );
    assert_eq!(
        script.matches("document.createElement('script')").count(),
        1
    );
    assert_eq!(
        script
            .matches("document.head.appendChild(mathjaxScript)")
            .count(),
        1
    );
    assert!(script.find("window.MathJax =").unwrap() < script.find("appendChild").unwrap());
    assert!(script.contains("displayOverflow: 'overflow'"));
    assert!(script.contains("inlineMath: [['\\\\(', '\\\\)']]"));
    assert!(script.contains("displayMath: [['\\\\[', '\\\\]']]"));
}

#[test]
fn view_styles_keep_headers_and_nested_choices_independent() {
    let css = read_asset("theme/dada.css");
    let options = css
        .split_once(".lean-selector .view-options {")
        .unwrap()
        .1
        .split_once('}')
        .unwrap()
        .0;
    assert!(options.contains("margin-left:auto"));
    // A nested diagram's radio button must not switch its enclosing Lean block.
    // The selector reaches the block's own header, then changes only its children.
    for pane in [".lean-source", ".lean-grammar", ".lean-markdown-body"] {
        assert!(css.contains(&format!(
            ".lean-group:has(> .lean-selector input:is([value=\"lean\"], [value=\"rust\"]):checked) > {pane}"
        )));
    }
    assert!(css.contains(
        ".heap-figure:has(input[value=\"facts\"]:checked) .heap-facts { display:block; }"
    ));
    assert!(css.contains(
        ".heap-figure:has(input[value=\"facts\"]:checked) .heap-diagram { display:none; }"
    ));
    for selector in [".lean-grammar", ".lean-source pre", ".heap-figure"] {
        let declaration = css
            .split_once(&format!("{selector} {{"))
            .unwrap()
            .1
            .split_once('}')
            .unwrap()
            .0;
        assert!(declaration.contains("overflow-x:auto"), "{selector}");
    }

    let mut book = json!({"items": [{"Chapter": {
        "path": "local.md", "content": "{anchor}`local.identity`\n\n{anchor-ref}`local.identity`", "sub_items": []
    }}]});
    process(&mut book).unwrap();
    let rendered = book["items"][0]["Chapter"]["content"].as_str().unwrap();
    assert_eq!(rendered.matches("class=\"spec-shield\"").count(), 2);
    assert!(rendered.contains("href=\"#claim-local.identity\""));
    assert!(!rendered.contains("<img"));
    assert!(!rendered.contains("src="));
    assert!(
        !css.contains("url("),
        "shield styling must not fetch a remote badge"
    );
}

#[test]
fn diagram_forward_references_and_aliases_preserve_distinct_edges() {
    let forward = r#"
# References and lease supports may precede their declarations.
vars.α = owned(a)
vars.β = leased(vars.α)
vars.γ = shared(b)
vars.δ = showned(b)

vars = variables()
a = object(Container)
b = primitive(1)
"#;
    let canonical = "vars = variables()\na = object(Container)\nb = primitive(1)\nvars.α = owned(a)\nvars.β = lease(vars.α)\nvars.γ = shlease(b)\nvars.δ = showned(b)";
    let svg = graph::render(forward).unwrap();
    let canonical_svg = graph::render(canonical).unwrap();
    // The accessible description retains the authored facts; only the diagram
    // after that description should be identical across the two spellings.
    assert!(svg.contains(&format!("<desc>{}</desc>", mdbook_dada::escape(forward))));
    assert_eq!(
        svg.split_once("</desc>").unwrap().1,
        canonical_svg.split_once("</desc>").unwrap().1
    );
    for kind in ["owned", "leased", "shlease", "showned"] {
        assert_eq!(
            svg.matches(&format!("class=\"heap-edge {kind}\"")).count(),
            1
        );
    }
    assert_eq!(svg.matches("class=\"heap-junction\"").count(), 1);
    for field in ["α", "β", "γ", "δ"] {
        assert!(svg.contains(&format!(">{field}</text>")));
    }
}

#[test]
fn diagram_array_size_boundary_preserves_all_slots() {
    let empty = graph::render("a = array(0)").unwrap();
    assert!(empty.contains("length 0"));
    assert!(!empty.contains("uninitialized"));
    let maximum = graph::render("a = array(64)").unwrap();
    assert_eq!(maximum.matches(": uninitialized</text>").count(), 64);
    for index in 0..64 {
        assert!(maximum.contains(&format!(">[{index}]: uninitialized</text>")));
    }
    let last = graph::render("a = array(64)\na[63] = owned(b)\nb = primitive(1)").unwrap();
    assert_eq!(last.matches(": uninitialized</text>").count(), 63);
    assert_eq!(last.matches("class=\"heap-edge owned\"").count(), 1);
    let too_large = graph::render("a = array(65)").unwrap_err();
    assert!(format!("{too_large:#}").contains("limited to 64 slots"));
    assert!(graph::render("a = array(64)\na[64] = uninitialized()").is_err());
}

#[cfg(unix)]
#[test]
fn lean_citations_accept_subdirectories_but_reject_source_root_escapes() {
    use mdbook_dada::{lean, units::UnitKind};
    use std::os::unix::fs::symlink;

    struct Sources(PathBuf);
    impl Drop for Sources {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }
    let path = std::env::temp_dir().join(format!(
        "dada-renderer-paths-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    fs::create_dir(&path).unwrap();
    let fixture = Sources(path);
    let root = fixture.0.join("lean");
    fs::create_dir_all(root.join("nested")).unwrap();
    fs::create_dir(fixture.0.join("outside")).unwrap();
    for path in [
        root.join("nested/Model.lean"),
        root.join("nested/Model.txt"),
        fixture.0.join("outside/Model.lean"),
    ] {
        fs::write(path, "def answer : Nat := 7\n").unwrap();
    }
    let explicit = lean::select(&root, "nested/Model.lean:answer", UnitKind::Definition).unwrap();
    let inferred = lean::select(&root, "nested/Model:answer", UnitKind::Definition).unwrap();
    assert_eq!(explicit.selected, "def answer : Nat := 7");
    assert_eq!(inferred.selected, explicit.selected);
    assert_eq!(
        inferred.path,
        root.join("nested/Model.lean").canonicalize().unwrap()
    );

    symlink(
        fixture.0.join("outside/Model.lean"),
        root.join("file-link.lean"),
    )
    .unwrap();
    symlink(fixture.0.join("outside"), root.join("directory-link")).unwrap();
    let absolute = format!("{}:answer", root.join("nested/Model.lean").display());
    for (target, diagnostic) in [
        ("../outside/Model.lean:answer", "relative without traversal"),
        (absolute.as_str(), "relative without traversal"),
        ("nested/Model.txt:answer", "expected a .lean file"),
        ("file-link:answer", "escapes configured directory"),
        (
            "directory-link/Model:answer",
            "escapes configured directory",
        ),
    ] {
        let error = lean::select(&root, target, UnitKind::Definition).unwrap_err();
        assert!(
            format!("{error:#}").contains(diagnostic),
            "{target}: {error:#}"
        );
    }
}

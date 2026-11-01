//! Exact source selections for named, unexpanded Rust items.
//!
//! Citations use `relative/file.rs:module::Type::method`. Inline modules are
//! traversed, but external modules and macros are not expanded. Conditional
//! compilation is not evaluated: ambiguous names are rejected even if a build
//! would select just one of them. The complete file is returned as context for
//! selections such as methods whose meaning depends on their enclosing impl.

use std::path::{Component, Path, PathBuf};

use anyhow::{bail, ensure, Context, Result};
use proc_macro2::Span;
use syn::{spanned::Spanned, ImplItem, Item, TraitItem, Type};

/// A source item and the complete file from which it was selected.
#[derive(Clone, Debug)]
pub struct Selection {
    /// Canonical path, guaranteed to remain within the supplied source root.
    pub path: PathBuf,
    pub source: String,
    /// Original source bytes, including the item's attributes and complete body.
    pub selected: String,
    /// Whether this exact item is a free function carrying the built-in test attribute.
    pub is_test: bool,
}

/// Select exactly one named Rust item, without interpreting or executing it.
pub fn select(root: &Path, target: &str) -> Result<Selection> {
    let (file, name) = target
        .split_once(':')
        .with_context(|| format!("Rust citation `{target}` must be `file.rs:Name`"))?;
    let relative = Path::new(file);
    ensure!(
        !relative.as_os_str().is_empty()
            && relative
                .components()
                .all(|part| matches!(part, Component::Normal(_) | Component::CurDir)),
        "Rust citation path `{file}` must be relative and cannot contain `..`"
    );
    ensure!(
        relative
            .extension()
            .is_some_and(|extension| extension == "rs"),
        "Rust citation `{target}` must name a `.rs` file"
    );
    let parsed_name = syn::parse_str::<syn::Path>(name)
        .with_context(|| format!("invalid Rust item name `{name}` in citation `{target}`"))?;
    ensure!(
        parsed_name.leading_colon.is_none()
            && parsed_name
                .segments
                .iter()
                .all(|part| matches!(part.arguments, syn::PathArguments::None)),
        "Rust citation name `{name}` must be an unparameterized item path"
    );
    let root = root
        .canonicalize()
        .with_context(|| format!("cannot locate Rust source root {}", root.display()))?;
    let path = root
        .join(relative)
        .canonicalize()
        .with_context(|| format!("cannot locate Rust source `{file}`"))?;
    ensure!(
        path.starts_with(&root),
        "Rust citation `{target}` escapes its source root through a symlink"
    );
    let source = std::fs::read_to_string(&path)
        .with_context(|| format!("cannot read Rust source {}", path.display()))?;
    let (selected, is_test) = select_source_item(&source, name)
        .with_context(|| format!("cannot select Rust citation `{target}`"))?;
    Ok(Selection {
        path,
        source,
        selected,
        is_test,
    })
}

#[cfg(test)]
fn select_source(source: &str, name: &str) -> Result<String> {
    Ok(select_source_item(source, name)?.0)
}

fn select_source_item(source: &str, name: &str) -> Result<(String, bool)> {
    let file = syn::parse_file(source).context("invalid Rust source")?;
    let mut selections = Vec::new();
    collect_items(&file.items, "", name, &mut selections);
    let (span, is_test) = match selections.as_slice() {
        [] => bail!("no named Rust item `{name}` exists in this file"),
        [selection] => *selection,
        _ => bail!("multiple Rust items named `{name}` exist in this file"),
    };
    source
        .get(span.byte_range())
        .map(|selected| (selected.to_owned(), is_test))
        .context("Rust item span does not identify valid UTF-8 source bytes")
}

fn qualified(prefix: &str, name: impl std::fmt::Display) -> String {
    if prefix.is_empty() {
        name.to_string()
    } else {
        format!("{prefix}::{name}")
    }
}

fn retain_match(
    name: &str,
    target: &str,
    span: Span,
    is_test: bool,
    selections: &mut Vec<(Span, bool)>,
) {
    if name == target {
        selections.push((span, is_test));
    }
}

fn collect_items(items: &[Item], prefix: &str, target: &str, selections: &mut Vec<(Span, bool)>) {
    for item in items {
        let ident = match item {
            Item::Const(item) => Some(&item.ident),
            Item::Enum(item) => Some(&item.ident),
            Item::Fn(item) => Some(&item.sig.ident),
            Item::Macro(item) => item.ident.as_ref(),
            Item::Mod(item) => Some(&item.ident),
            Item::Static(item) => Some(&item.ident),
            Item::Struct(item) => Some(&item.ident),
            Item::Trait(item) => Some(&item.ident),
            Item::TraitAlias(item) => Some(&item.ident),
            Item::Type(item) => Some(&item.ident),
            Item::Union(item) => Some(&item.ident),
            _ => None,
        };
        if let Some(ident) = ident {
            let is_test = match item {
                Item::Fn(function) => function.attrs.iter().any(
                    |attr| matches!(&attr.meta, syn::Meta::Path(path) if path.is_ident("test")),
                ),
                _ => false,
            };
            retain_match(
                &qualified(prefix, ident),
                target,
                item.span(),
                is_test,
                selections,
            );
        }
        match item {
            Item::Mod(module) => {
                if let Some((_, items)) = &module.content {
                    collect_items(items, &qualified(prefix, &module.ident), target, selections);
                }
            }
            Item::Impl(item) => {
                // A path self-type provides an explicit, stable citation name.
                // Generic parameters are omitted, just as in ordinary Rust paths.
                if let Type::Path(self_type) = item.self_ty.as_ref() {
                    if self_type.qself.is_none() {
                        let name = self_type
                            .path
                            .segments
                            .iter()
                            .map(|part| part.ident.to_string())
                            .collect::<Vec<_>>()
                            .join("::");
                        let prefix = qualified(prefix, name);
                        for member in &item.items {
                            let ident = match member {
                                ImplItem::Const(item) => Some(&item.ident),
                                ImplItem::Fn(item) => Some(&item.sig.ident),
                                ImplItem::Type(item) => Some(&item.ident),
                                _ => None,
                            };
                            if let Some(ident) = ident {
                                retain_match(
                                    &qualified(&prefix, ident),
                                    target,
                                    member.span(),
                                    false,
                                    selections,
                                );
                            }
                        }
                    }
                }
            }
            Item::Trait(item) => {
                let prefix = qualified(prefix, &item.ident);
                for member in &item.items {
                    let ident = match member {
                        TraitItem::Const(item) => Some(&item.ident),
                        TraitItem::Fn(item) => Some(&item.sig.ident),
                        TraitItem::Type(item) => Some(&item.ident),
                        _ => None,
                    };
                    if let Some(ident) = ident {
                        retain_match(
                            &qualified(&prefix, ident),
                            target,
                            member.span(),
                            false,
                            selections,
                        );
                    }
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    struct Fixture(PathBuf);

    impl Fixture {
        fn new() -> Self {
            static NEXT: AtomicUsize = AtomicUsize::new(0);
            let path = std::env::temp_dir().join(format!(
                "dada-rust-source-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            std::fs::create_dir(&path).unwrap();
            std::fs::write(path.join("items.rs"), "pub fn checked() {}\n").unwrap();
            Self(path)
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }

    #[test]
    fn selects_complete_test_with_attributes_and_unicode() {
        let source = "// fn checked() { comment decoy } α\nconst TEXT: &str = \"fn checked() {} β\";\n\n#[test]\n#[ignore = \"γ\"]\nfn checked() {\n    let δ = \"ε\";\n    assert_eq!(δ, \"ε\");\n}\nfn later() {}\n";
        assert_eq!(
            select_source(source, "checked").unwrap(),
            "#[test]\n#[ignore = \"γ\"]\nfn checked() {\n    let δ = \"ε\";\n    assert_eq!(δ, \"ε\");\n}"
        );
    }

    #[test]
    fn selects_module_qualified_functions_methods_and_types() {
        let source = "mod nested {\n    pub struct Store<T>(T);\n    impl<T> Store<T> {\n        /// Read an entry.\n        pub fn read(&self) -> &T { &self.0 }\n    }\n    #[test]\n    fn checked() {}\n}\n";
        assert_eq!(
            select_source(source, "nested::Store").unwrap(),
            "pub struct Store<T>(T);"
        );
        assert_eq!(
            select_source(source, "nested::Store::read").unwrap(),
            "/// Read an entry.\n        pub fn read(&self) -> &T { &self.0 }"
        );
        assert_eq!(
            select_source(source, "nested::checked").unwrap(),
            "#[test]\n    fn checked() {}"
        );
        assert!(select_source(source, "checked").is_err());
        assert!(select_source(source, "nested")
            .unwrap()
            .starts_with("mod nested {"));
    }

    #[test]
    fn rejects_missing_ambiguous_and_generated_items() {
        assert!(select_source("fn found() {}", "missing").is_err());
        assert!(
            select_source("#[cfg(a)] fn same() {} #[cfg(b)] fn same() {}", "same")
                .unwrap_err()
                .to_string()
                .contains("multiple")
        );
        assert!(select_source(
            "struct T; impl T { fn same() {} } impl Trait for T { fn same() {} }",
            "T::same"
        )
        .is_err());
        assert!(select_source("generate! { fn generated() {} }", "generated").is_err());
        assert!(select_source("fn outer() { fn inner() {} }", "inner").is_err());
    }

    #[test]
    fn selects_named_data_and_trait_items_without_reformatting() {
        let source = "pub enum Mode { Unique, Shared }\nconst COUNT: usize = 2;\ntype Count = usize;\ntrait Read { fn read(&self); }\n";
        for (name, expected) in [
            ("Mode", "pub enum Mode { Unique, Shared }"),
            ("COUNT", "const COUNT: usize = 2;"),
            ("Count", "type Count = usize;"),
            ("Read", "trait Read { fn read(&self); }"),
            ("Read::read", "fn read(&self);"),
        ] {
            assert_eq!(select_source(source, name).unwrap(), expected);
        }
        assert!(select_source("fn broken( {", "broken").is_err());
    }

    #[test]
    fn rejects_unsafe_paths_and_non_rust_files() {
        let fixture = Fixture::new();
        for target in [
            "items.rs",
            "items.rs:",
            "items.rs:checked::<u8>",
            "items.rs:::checked",
            "../items.rs:checked",
            "/items.rs:checked",
            "items.txt:checked",
            "absent.rs:checked",
        ] {
            assert!(select(&fixture.0, target).is_err(), "accepted {target}");
        }
        let selected = select(&fixture.0, "items.rs:checked").unwrap();
        assert_eq!(selected.selected, "pub fn checked() {}");
        assert_eq!(selected.source, "pub fn checked() {}\n");
        assert_eq!(
            selected.path,
            fixture.0.join("items.rs").canonicalize().unwrap()
        );
    }

    #[cfg(unix)]
    #[test]
    fn rejects_symlinks_outside_root() {
        let fixture = Fixture::new();
        let other = Fixture::new();
        std::os::unix::fs::symlink(other.0.join("items.rs"), fixture.0.join("escape.rs")).unwrap();
        assert!(select(&fixture.0, "escape.rs:checked")
            .unwrap_err()
            .to_string()
            .contains("escapes"));
    }
}

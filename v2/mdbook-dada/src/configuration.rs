//! Shared source configuration for rendering and correspondence inputs.
use crate::{inventory, units};
use anyhow::{ensure, Context, Result};
use serde::Deserialize;
use serde_json::Value;
use std::{
    fs,
    path::{Path, PathBuf},
};

#[derive(Debug, Deserialize, PartialEq, Eq)]
pub struct SourceConfiguration {
    book: Book,
    preprocessor: Preprocessors,
}

#[derive(Debug, Deserialize, PartialEq, Eq)]
struct Book {
    src: String,
}

#[derive(Debug, Deserialize, PartialEq, Eq)]
struct Preprocessors {
    dada: Dada,
}

#[derive(Debug, Deserialize, PartialEq, Eq)]
struct Dada {
    #[serde(rename = "lean-source")]
    lean_source: String,
}

impl SourceConfiguration {
    pub fn load(root: &Path) -> Result<Self> {
        let configuration = toml::from_str(
            &fs::read_to_string(root.join("book.toml")).context("reading book.toml")?,
        )
        .context("parsing book.toml source configuration")?;
        Ok(configuration)
    }

    pub fn lean_root(&self, root: &Path) -> Result<PathBuf> {
        inventory::input_path(root, &self.preprocessor.dada.lean_source)
    }

    pub fn markdown_root(&self, root: &Path) -> Result<PathBuf> {
        inventory::input_path(root, &self.book.src)
    }

    /// Runtime overrides may not make the renderer select different source
    /// trees from the book.toml snapshot used by the evidence inventory.
    pub fn check_context(&self, context: &Value) -> Result<()> {
        let effective: Self = serde_json::from_value(context["config"].clone())
            .context("reading mdBook source configuration")?;
        ensure!(self == &effective,
            "mdBook source configuration differs from book.toml; update book.toml rather than overriding book.src or preprocessor.dada.lean-source");
        Ok(())
    }

    /// Check original chapters even if mdBook's links preprocessor has already
    /// expanded an include. Also prevent preprocessing from adding, deleting,
    /// or changing a reviewed unit behind the inventory's back.
    pub fn validate_chapters(&self, root: &Path, book: &Value) -> Result<()> {
        let source_root = self.markdown_root(root)?;
        let key = if book.get("items").is_some_and(Value::is_array) {
            "items"
        } else {
            "sections"
        };
        crate::walk(&book[key], &mut |chapter| {
            let path = chapter["source_path"]
                .as_str()
                .or_else(|| chapter["path"].as_str())
                .context("chapter has no source path")?;
            let source_path = source_root.join(path);
            let name = inventory::relative_path(root, &source_path)?;
            let source_path = inventory::input_path(root, &name)?;
            let original = fs::read_to_string(source_path)?;
            let authored = units::parse(&original, &name)?;
            let processed = units::parse(
                chapter["content"]
                    .as_str()
                    .context("chapter has no content")?,
                &name,
            )?;
            ensure!(authored.iter().map(|unit| (&unit.id, &unit.raw)).eq(
                processed.iter().map(|unit| (&unit.id, &unit.raw))),
                "{name}: preprocessing changed structured units; includes and other external substitutions cannot supply or alter reviewed content");
            Ok(())
        })
    }
}

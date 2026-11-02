//! The current, independently derived specification inventory and review inputs.
use crate::{
    configuration::SourceConfiguration,
    lean, rust_source,
    units::{self, SpecUnit},
};
use anyhow::{bail, ensure, Context, Result};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path, PathBuf},
};

pub const SCHEMA: u32 = 1;

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Config {
    pub schema: u32,
    pub chapters: Vec<String>,
    pub policies: Vec<String>,
    #[serde(default)]
    pub context: Vec<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Input {
    pub key: String,
    pub path: String,
    pub line: usize,
    pub content: String,
    pub sha256: String,
}

impl Input {
    pub fn new(key: String, path: String, line: usize, content: String) -> Self {
        let sha256 = hash(content.as_bytes());
        Self {
            key,
            path,
            line,
            content,
            sha256,
        }
    }

    /// Context snapshots are available to reviewers, without asserting that every
    /// unrelated declaration or proof in a conservatively captured file was read.
    pub fn requires_examination(&self) -> bool {
        [
            "unit:", "lean:", "rust:", "test:", "policy:", "extra:", "audit:",
        ]
        .iter()
        .any(|prefix| self.key.starts_with(prefix))
    }
}

pub fn hash(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

/// Existing input paths must be relative, canonical, and contained in the project.
/// Evidence output may never become its own input.
pub fn input_path(root: &Path, relative: &str) -> Result<PathBuf> {
    let path = Path::new(relative);
    ensure!(
        !path.as_os_str().is_empty()
            && path
                .components()
                .all(|part| matches!(part, Component::Normal(_))),
        "input path must be a normal relative path: {relative}"
    );
    ensure!(
        !path.starts_with("evidence") && !path.starts_with("target") && !path.starts_with("book"),
        "generated output cannot be a review input: {relative}"
    );
    let canonical = root
        .join(path)
        .canonicalize()
        .with_context(|| format!("resolving input {relative}"))?;
    ensure!(
        canonical.starts_with(root),
        "input escapes project: {relative}"
    );
    let resolved = canonical.strip_prefix(root)?;
    ensure!(
        !resolved.starts_with("evidence")
            && !resolved.starts_with("target")
            && !resolved.starts_with("book"),
        "generated output cannot be a review input: {relative}"
    );
    Ok(canonical)
}

pub fn relative_path(root: &Path, path: &Path) -> Result<String> {
    Ok(path
        .strip_prefix(root)
        .context("source is outside the project")?
        .to_str()
        .context("source path is not UTF-8")?
        .replace('\\', "/"))
}

fn files(root: &Path, directory: &Path, extension: &str) -> Result<Vec<PathBuf>> {
    let mut result = Vec::new();
    for entry in
        fs::read_dir(directory).with_context(|| format!("reading {}", directory.display()))?
    {
        let entry = entry?;
        let path = entry.path();
        // Markdown is the specification inventory, including explicitly linked
        // hidden chapters. Lean/tool scans still omit generated hidden trees
        // such as `.lake`; a filename convention must not hide a review unit.
        if extension != "md" && entry.file_name().to_string_lossy().starts_with('.') {
            continue;
        }
        ensure!(
            !entry.file_type()?.is_symlink(),
            "source directory contains a symbolic link: {}",
            path.display()
        );
        ensure!(path.starts_with(root), "source path escapes project");
        if path.is_dir() {
            result.extend(files(root, &path, extension)?);
        } else if path.extension().is_some_and(|ext| ext == extension) {
            result.push(path);
        }
    }
    result.sort();
    Ok(result)
}

pub struct Inventory {
    pub root: PathBuf,
    pub config: Config,
    pub source_configuration: SourceConfiguration,
    pub units: BTreeMap<String, SpecUnit>,
    pub required: BTreeSet<String>,
    pub sources: BTreeMap<String, String>,
}

impl Inventory {
    pub fn load(root: &Path) -> Result<Self> {
        let root = root
            .canonicalize()
            .context("resolving specification root")?;
        let config: Config = serde_json::from_str(
            &fs::read_to_string(root.join("spec.json")).context("reading spec.json")?,
        )
        .context("parsing spec.json")?;
        ensure!(
            config.schema == SCHEMA,
            "unsupported specification schema {}",
            config.schema
        );
        ensure!(
            !config.chapters.is_empty(),
            "spec.json must name at least one strict chapter"
        );
        ensure!(
            !config.policies.is_empty(),
            "spec.json must name a review policy"
        );
        let source_configuration = SourceConfiguration::load(&root)?;
        source_configuration.lean_root(&root)?;
        let mut units = BTreeMap::new();
        let mut sources = BTreeMap::new();
        for path in files(&root, &source_configuration.markdown_root(&root)?, "md")? {
            let name = relative_path(&root, &path)?;
            let source = fs::read_to_string(&path)?;
            for unit in units::parse(&source, &name)? {
                ensure!(
                    !units.contains_key(&unit.id),
                    "duplicate unit ID {}",
                    unit.id
                );
                units.insert(unit.id.clone(), unit);
            }
            sources.insert(name, source);
        }
        let mut required = BTreeSet::new();
        let mut chapters = BTreeSet::new();
        for chapter in &config.chapters {
            input_path(&root, chapter)?;
            ensure!(
                chapters.insert(chapter),
                "duplicate strict chapter {chapter}"
            );
            let source = sources
                .get(chapter)
                .with_context(|| format!("strict chapter is not Markdown under md/: {chapter}"))?;
            units::validate_coverage(source, chapter)?;
            let ids: Vec<_> = units
                .values()
                .filter(|unit| &unit.source_path == chapter)
                .map(|unit| unit.id.clone())
                .collect();
            ensure!(!ids.is_empty(), "strict chapter has no units: {chapter}");
            required.extend(ids);
        }
        // A new-style unit always participates, even before its chapter becomes
        // strict about free-floating prose. Legacy directives are not units.
        required.extend(units.keys().cloned());
        for unit in units.values() {
            for dependency in &unit.uses {
                ensure!(
                    units.contains_key(dependency),
                    "{}: {} uses missing unit {dependency}",
                    unit.source_path,
                    unit.id
                );
            }
        }
        for path in config.policies.iter().chain(&config.context) {
            input_path(&root, path)?;
        }
        let inventory = Self {
            root,
            config,
            source_configuration,
            units,
            required,
            sources,
        };
        // Resolve authored URLs against actual chapter locations. Checking only
        // global IDs misses wrong-chapter links and excludes legacy anchors.
        crate::links::Links::build(&inventory)?;
        Ok(inventory)
    }

    fn file_input(&self, key: String, name: &str) -> Result<Input> {
        let path = input_path(&self.root, name)?;
        Ok(Input::new(
            key,
            name.to_owned(),
            1,
            fs::read_to_string(&path).with_context(|| format!("reading input {name}"))?,
        ))
    }

    fn add_unit(
        &self,
        id: &str,
        inputs: &mut BTreeMap<String, Input>,
        visited: &mut BTreeSet<String>,
    ) -> Result<()> {
        if !visited.insert(id.to_owned()) {
            return Ok(());
        }
        let unit = self
            .units
            .get(id)
            .with_context(|| format!("unknown unit {id}"))?;
        let source = &self.sources[&unit.source_path];
        let line = source[..unit.range.start]
            .bytes()
            .filter(|b| *b == b'\n')
            .count()
            + 1;
        let input = Input::new(
            format!("unit:{id}"),
            unit.source_path.clone(),
            line,
            unit.raw.clone(),
        );
        inputs.insert(input.key.clone(), input);
        for target in &unit.lean {
            let selected = lean::select(
                &self.source_configuration.lean_root(&self.root)?,
                target,
                unit.kind,
            )
            .with_context(|| format!("{}: {id} citation {target}", unit.source_path))?;
            let path = relative_path(&self.root, &selected.path)?;
            let offset = selected.source.find(&selected.selected).unwrap_or(0);
            let line = selected.source[..offset]
                .bytes()
                .filter(|b| *b == b'\n')
                .count()
                + 1;
            let input = Input::new(format!("lean:{target}"), path, line, selected.selected);
            inputs.insert(input.key.clone(), input);
        }
        for (prefix, targets) in [("rust", &unit.rust), ("test", &unit.tests)] {
            for target in targets {
                let selected = rust_source::select(&self.root, target)
                    .with_context(|| format!("{}: {id} citation {target}", unit.source_path))?;
                if prefix == "test" {
                    ensure!(
                        selected.is_test,
                        ":tests: target must be a #[test] function: {target}"
                    );
                }
                let path = relative_path(&self.root, &selected.path)?;
                let offset = selected.source.find(&selected.selected).unwrap_or(0);
                let line = selected.source[..offset]
                    .bytes()
                    .filter(|b| *b == b'\n')
                    .count()
                    + 1;
                let input = Input::new(
                    format!("{prefix}:{target}"),
                    path.clone(),
                    line,
                    selected.selected,
                );
                inputs.insert(input.key.clone(), input);
                let context = self.file_input(format!("context:{path}"), &path)?;
                inputs.insert(context.key.clone(), context);
            }
        }
        let linked = units::linked_ids(&unit.body)?;
        for dependency in unit
            .uses
            .iter()
            .chain(linked.iter().filter(|id| self.units.contains_key(*id)))
        {
            self.add_unit(dependency, inputs, visited)?;
        }
        Ok(())
    }

    /// Derive required snapshots from current sources, never from a review record.
    pub fn inputs(&self, id: &str) -> Result<Vec<Input>> {
        if crate::link_audit::is_subject(id) {
            return crate::link_audit::inputs(self, id);
        }
        let mut inputs = BTreeMap::new();
        self.add_unit(id, &mut inputs, &mut BTreeSet::new())?;
        for input in self.common_inputs()? {
            inputs.insert(input.key.clone(), input);
        }
        if inputs.keys().any(|key| key.starts_with("lean:")) {
            let lean_root = self.source_configuration.lean_root(&self.root)?;
            for path in files(&self.root, &lean_root, "lean")? {
                let name = relative_path(&self.root, &path)?;
                let input = self.file_input(format!("context:{name}"), &name)?;
                inputs.insert(input.key.clone(), input);
            }
            for path in ["lean-toolchain", "lakefile.toml", "lake-manifest.json"] {
                let name = relative_path(&self.root, &lean_root.join(path))?;
                let input = self.file_input(format!("context:{name}"), &name)?;
                inputs.insert(input.key.clone(), input);
            }
        }
        Ok(inputs.into_values().collect())
    }

    /// Shared freshness inputs for correspondence and editorial audits. The
    /// subject-specific derivation supplies the material the reviewer examines.
    pub fn common_inputs(&self) -> Result<Vec<Input>> {
        let mut inputs = BTreeMap::new();
        for path in [
            "spec.json",
            "book.toml",
            "Cargo.toml",
            "Cargo.lock",
            "mdbook-dada/Cargo.toml",
        ] {
            let input = self.file_input(format!("tool:{path}"), path)?;
            inputs.insert(input.key.clone(), input);
        }
        for (directory, extension) in [
            ("mdbook-dada/src", "rs"),
            ("mdbook-dada/tests", "rs"),
            ("mdbook-dada/tests", "lean"),
        ] {
            for path in files(&self.root, &self.root.join(directory), extension)? {
                let name = relative_path(&self.root, &path)?;
                let input = self.file_input(format!("tool:{name}"), &name)?;
                inputs.insert(input.key.clone(), input);
            }
        }
        // Presentation assets are implementation inputs too. Minimal external
        // fixtures may omit a theme; adding one changes the derived manifest.
        if self.root.join("theme").exists() {
            for extension in ["js", "css"] {
                for path in files(&self.root, &self.root.join("theme"), extension)? {
                    let name = relative_path(&self.root, &path)?;
                    let input = self.file_input(format!("tool:{name}"), &name)?;
                    inputs.insert(input.key.clone(), input);
                }
            }
        }
        for (prefix, paths) in [
            ("policy", &self.config.policies),
            ("context", &self.config.context),
        ] {
            for path in paths {
                let input = self.file_input(format!("{prefix}:{path}"), path)?;
                inputs.insert(input.key.clone(), input);
            }
        }
        Ok(inputs.into_values().collect())
    }

    pub fn extra_input(&self, path: &str) -> Result<Input> {
        self.file_input(format!("extra:{path}"), path)
    }

    pub fn unit(&self, id: &str) -> Result<&SpecUnit> {
        self.units
            .get(id)
            .with_context(|| format!("unknown unit {id}"))
    }
}

pub fn find_root(start: &Path) -> Result<PathBuf> {
    for parent in start.ancestors() {
        for candidate in [parent.to_path_buf(), parent.join("v2")] {
            if candidate.join("spec.json").is_file() {
                return Ok(candidate);
            }
        }
    }
    bail!("cannot find spec.json; run from the repository or v2 directory")
}

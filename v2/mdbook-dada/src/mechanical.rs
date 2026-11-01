//! Recorded command execution, separate from correspondence decisions.
//!
//! Only `run` executes a process. Reading and checking saved receipts is syntactic.
use crate::{
    evidence::write_immutable,
    inventory::{hash, input_path, relative_path, Input},
};
use anyhow::{bail, ensure, Context, Result};
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::{Instant, SystemTime, UNIX_EPOCH},
};

const CONFIG: &str = "spec-checks.json";
const RECORDS: &str = "evidence/executions";
const SCHEMA: u32 = 1;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Check {
    pub description: String,
    /// Project-relative directory, or `.` for the project root.
    pub cwd: String,
    pub command: Vec<String>,
    pub version: Vec<String>,
    /// Complete files or directories. Generated directories are not inputs.
    pub inputs: Vec<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Configuration {
    pub schema: u32,
    pub checks: BTreeMap<String, Check>,
}

impl Configuration {
    pub fn load(root: &Path) -> Result<Self> {
        let source = input_path(root, CONFIG)?;
        let config: Self = read_json(&source)?;
        ensure!(
            config.schema == SCHEMA,
            "unsupported mechanical-check schema"
        );
        ensure!(!config.checks.is_empty(), "no mechanical checks configured");
        for (name, check) in &config.checks {
            ensure!(
                !name.is_empty()
                    && name
                        .bytes()
                        .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_'),
                "invalid check name {name}"
            );
            validate_check(check)?;
            working_directory(root, &check.cwd)?;
        }
        Ok(config)
    }
}

fn validate_check(check: &Check) -> Result<()> {
    ensure!(
        check.cwd == "." || normal_path(&check.cwd),
        "check working directory must stay within project sources"
    );
    ensure!(
        !check.description.trim().is_empty(),
        "check needs a description"
    );
    for argv in [&check.command, &check.version] {
        ensure!(
            !argv.is_empty() && !argv[0].trim().is_empty(),
            "check needs command and version argv"
        );
        ensure!(
            argv.iter().all(|arg| !arg.contains('\0')),
            "command contains a NUL byte"
        );
    }
    ensure!(!check.inputs.is_empty(), "check needs source inputs");
    ensure!(
        check.inputs.iter().all(|path| normal_path(path)),
        "check input roots must be normal source paths"
    );
    Ok(())
}

fn working_directory(root: &Path, relative: &str) -> Result<PathBuf> {
    let path = if relative == "." {
        root.to_owned()
    } else {
        input_path(root, relative)?
    };
    ensure!(path.is_dir(), "check working directory is not a directory");
    Ok(path)
}

fn generated(path: &Path) -> bool {
    path.components().any(|part| {
        [".git", ".lake", "target", "book", "evidence"]
            .iter()
            .any(|name| part.as_os_str() == *name)
    })
}

fn collect(root: &Path, path: &Path, inputs: &mut BTreeMap<String, Input>) -> Result<()> {
    let relative = path
        .strip_prefix(root)
        .context("mechanical input outside project")?;
    if generated(relative) {
        return Ok(());
    }
    let name = relative_path(root, path)?;
    let metadata =
        fs::symlink_metadata(path).with_context(|| format!("reading input {}", path.display()))?;
    ensure!(
        !metadata.file_type().is_symlink(),
        "mechanical source tree contains a symbolic link: {}",
        path.display()
    );
    let (kind, content) = if metadata.is_dir() {
        let mut children = Vec::new();
        for entry in fs::read_dir(path)? {
            let child = entry?.path();
            if generated(child.strip_prefix(root)?) {
                continue;
            }
            children.push(
                child
                    .file_name()
                    .context("input has no name")?
                    .to_str()
                    .context("input filename is not UTF-8")?
                    .to_owned(),
            );
            collect(root, &child, inputs)?;
        }
        children.sort();
        ("directory", serde_json::to_string(&children)?)
    } else {
        ensure!(metadata.is_file(), "mechanical input is not a regular file");
        (
            "file",
            fs::read_to_string(path).with_context(|| format!("reading mechanical input {name}"))?,
        )
    };
    inputs.insert(
        name.clone(),
        Input::new(format!("{kind}:{name}"), name, 1, content),
    );
    Ok(())
}

fn normal_path(path: &str) -> bool {
    !path.is_empty()
        && Path::new(path)
            .components()
            .all(|part| matches!(part, std::path::Component::Normal(_)))
        && !generated(Path::new(path))
}

fn validate_snapshot(inputs: &[Input], check: &Check) -> Result<()> {
    let mut previous: Option<&str> = None;
    let mut by_path = BTreeMap::new();
    for input in inputs {
        ensure!(
            normal_path(&input.path)
                && input.line == 1
                && input.sha256 == hash(input.content.as_bytes()),
            "invalid execution input {}",
            input.key
        );
        ensure!(
            previous.is_none_or(|p| p < input.path.as_str()),
            "execution inputs are duplicated or out of order"
        );
        previous = Some(&input.path);
        by_path.insert(input.path.as_str(), input);
    }
    let mut pending: Vec<String> = check.inputs.clone();
    pending.extend([CONFIG.to_owned(), "mdbook-dada/src".to_owned()]);
    let mut visited = BTreeSet::new();
    while let Some(path) = pending.pop() {
        if !visited.insert(path.clone()) {
            continue;
        }
        let input = by_path
            .get(path.as_str())
            .with_context(|| format!("execution omits required input {path}"))?;
        if input.key == format!("directory:{path}") {
            let children: Vec<String> =
                serde_json::from_str(&input.content).context("parsing directory membership")?;
            ensure!(
                children.windows(2).all(|pair| pair[0] < pair[1]),
                "directory membership is duplicated or out of order"
            );
            for child in children {
                ensure!(
                    normal_path(&child) && Path::new(&child).components().count() == 1,
                    "invalid directory entry"
                );
                pending.push(format!("{path}/{child}"));
            }
        } else {
            ensure!(input.key == format!("file:{path}"), "invalid input kind");
        }
    }
    ensure!(visited.len() == inputs.len(), "unexpected execution input");
    ensure!(
        by_path[CONFIG].key == format!("file:{CONFIG}"),
        "check configuration is not a file"
    );
    ensure!(
        by_path["mdbook-dada/src"].key == "directory:mdbook-dada/src",
        "runner source is not a directory"
    );
    Ok(())
}

/// Capture directory membership and complete UTF-8 source contents, in path order.
/// Versioned profiles and runner sources are always included independently of inputs.
pub fn snapshot(root: &Path, check: &Check) -> Result<Vec<Input>> {
    let mut inputs = BTreeMap::new();
    for relative in check
        .inputs
        .iter()
        .map(String::as_str)
        .chain([CONFIG, "mdbook-dada/src"])
    {
        let path = input_path(root, relative)?;
        ensure!(
            !generated(path.strip_prefix(root)?),
            "generated output cannot be a mechanical input"
        );
        // Inspect the lexical path as well, so a selected symlink is not followed.
        let mut lexical = root.to_owned();
        for component in Path::new(relative).components() {
            lexical.push(component);
            ensure!(
                !fs::symlink_metadata(&lexical)?.file_type().is_symlink(),
                "mechanical input uses a symbolic link"
            );
        }
        collect(root, &path, &mut inputs)?;
    }
    Ok(inputs.into_values().collect())
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Outcome {
    pub exit_code: Option<i32>,
    /// Raw bytes preserve non-UTF-8 diagnostics too.
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub launch_error: Option<String>,
}

impl Outcome {
    fn succeeded(&self) -> bool {
        self.exit_code == Some(0) && self.launch_error.is_none()
    }
}

fn execute(argv: &[String], cwd: &Path) -> Outcome {
    match Command::new(&argv[0])
        .args(&argv[1..])
        .current_dir(cwd)
        .output()
    {
        Ok(output) => Outcome {
            exit_code: output.status.code(),
            stdout: output.stdout,
            stderr: output.stderr,
            launch_error: None,
        },
        Err(error) => Outcome {
            exit_code: None,
            stdout: Vec::new(),
            stderr: Vec::new(),
            launch_error: Some(error.to_string()),
        },
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Execution {
    pub schema: u32,
    pub name: String,
    pub check: Check,
    pub host_os: String,
    pub host_arch: String,
    pub started_unix_ms: u128,
    pub finished_unix_ms: u128,
    pub elapsed_ms: u128,
    pub before: Vec<Input>,
    pub after: Option<Vec<Input>>,
    pub after_error: Option<String>,
    pub version_before: Outcome,
    pub command: Option<Outcome>,
    pub version_after: Outcome,
    pub digest: String,
}

impl Execution {
    fn content_digest(&self) -> Result<String> {
        let mut content = self.clone();
        content.digest.clear();
        Ok(hash(&serde_json::to_vec(&content)?))
    }

    /// A successful receipt also requires stable inputs and tool-version output.
    pub fn succeeded(&self) -> bool {
        self.version_before.succeeded()
            && self.version_after == self.version_before
            && self.command.as_ref().is_some_and(Outcome::succeeded)
            && self.after.as_ref() == Some(&self.before)
            && self.after_error.is_none()
    }

    pub fn validate(&self) -> Result<()> {
        ensure!(
            self.schema == SCHEMA && self.content_digest()? == self.digest,
            "execution digest or schema is invalid"
        );
        validate_check(&self.check)?;
        ensure!(!self.before.is_empty(), "execution has no input snapshots");
        ensure!(
            self.after.is_some() != self.after_error.is_some(),
            "execution needs an after snapshot or an error"
        );
        ensure!(
            self.command.is_some() == self.version_before.succeeded(),
            "execution command/version results are inconsistent"
        );
        for inputs in std::iter::once(&self.before).chain(self.after.iter()) {
            validate_snapshot(inputs, &self.check)?;
        }
        let config_input = self
            .before
            .iter()
            .find(|input| input.path == CONFIG)
            .context("missing check configuration")?;
        let config: Configuration = serde_json::from_str(&config_input.content)?;
        ensure!(
            config.schema == SCHEMA && config.checks.get(&self.name) == Some(&self.check),
            "recorded check differs from its configuration snapshot"
        );
        for outcome in [&self.version_before, &self.version_after]
            .into_iter()
            .chain(self.command.iter())
        {
            if let Some(error) = &outcome.launch_error {
                ensure!(
                    !error.is_empty()
                        && outcome.exit_code.is_none()
                        && outcome.stdout.is_empty()
                        && outcome.stderr.is_empty(),
                    "launch error has process output or exit code"
                );
            }
        }
        Ok(())
    }
}

fn now() -> Result<u128> {
    Ok(SystemTime::now().duration_since(UNIX_EPOCH)?.as_millis())
}

/// Execute only an explicitly selected configured check. Preserve failures as well
/// as successes; endpoint snapshots do not provide filesystem isolation.
pub fn run(root: &Path, name: &str) -> Result<PathBuf> {
    let root = root.canonicalize()?;
    let config = Configuration::load(&root)?;
    let check = config
        .checks
        .get(name)
        .with_context(|| format!("unknown mechanical check {name}"))?
        .clone();
    let cwd = working_directory(&root, &check.cwd)?;
    let before = snapshot(&root, &check)?;
    let started_unix_ms = now()?;
    let timer = Instant::now();
    let version_before = execute(&check.version, &cwd);
    let command = version_before
        .succeeded()
        .then(|| execute(&check.command, &cwd));
    let version_after = execute(&check.version, &cwd);
    let (after, after_error) = match snapshot(&root, &check) {
        Ok(inputs) => (Some(inputs), None),
        Err(error) => (None, Some(format!("{error:#}"))),
    };
    let mut receipt = Execution {
        schema: SCHEMA,
        name: name.into(),
        check,
        host_os: std::env::consts::OS.into(),
        host_arch: std::env::consts::ARCH.into(),
        started_unix_ms,
        finished_unix_ms: now()?,
        elapsed_ms: timer.elapsed().as_millis(),
        before,
        after,
        after_error,
        version_before,
        command,
        version_after,
        digest: String::new(),
    };
    receipt.digest = receipt.content_digest()?;
    receipt.validate()?;
    write_immutable(
        &root,
        &PathBuf::from(RECORDS).join(format!("{}.json", receipt.digest)),
        &receipt,
    )
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T> {
    serde_json::from_slice(&fs::read(path).with_context(|| format!("reading {}", path.display()))?)
        .with_context(|| format!("parsing {}", path.display()))
}

pub fn load(path: &Path) -> Result<Execution> {
    let receipt: Execution = read_json(path)?;
    receipt.validate()?;
    ensure!(
        path.file_stem().and_then(|s| s.to_str()) == Some(receipt.digest.as_str()),
        "execution filename differs from digest"
    );
    Ok(receipt)
}

/// Validate retained receipts without executing any commands, including historical
/// failures and receipts for checks no longer configured.
pub fn records(root: &Path) -> Result<Vec<Execution>> {
    let directory = root.join(RECORDS);
    if !directory.exists() {
        return Ok(Vec::new());
    }
    ensure!(
        directory.canonicalize()?.starts_with(root),
        "execution directory escapes project"
    );
    let mut records = Vec::new();
    for entry in fs::read_dir(directory)? {
        let path = entry?.path();
        ensure!(
            !fs::symlink_metadata(&path)?.file_type().is_symlink(),
            "execution receipt is a symbolic link"
        );
        if path.extension().is_some_and(|s| s == "json") {
            records.push(load(&path)?);
        }
    }
    Ok(records)
}

#[derive(Debug)]
pub struct Status {
    pub name: String,
    pub state: &'static str,
    pub receipt: Option<String>,
}

/// Report the latest receipt per configured check. A later failure or stale run
/// cannot be hidden by an older success. Local receipt timestamps are provenance,
/// not an authenticated clock.
pub fn status(root: &Path) -> Result<Vec<Status>> {
    let records = records(root)?;
    if !root.join(CONFIG).exists() {
        if records.is_empty() {
            return Ok(Vec::new());
        }
        bail!("execution receipts exist without {CONFIG}");
    }
    let config = Configuration::load(root)?;
    config
        .checks
        .into_iter()
        .map(|(name, check)| {
            let latest_time = records
                .iter()
                .filter(|r| r.name == name)
                .map(|r| r.finished_unix_ms)
                .max();
            let latest: Vec<_> = records
                .iter()
                .filter(|r| r.name == name && Some(r.finished_unix_ms) == latest_time)
                .collect();
            let current = snapshot(root, &check)?;
            let state = if latest.is_empty() {
                "not recorded"
            } else if latest
                .iter()
                .any(|r| r.check != check || r.before != current)
            {
                "stale"
            } else if latest.iter().any(|r| !r.succeeded()) {
                "recorded failure"
            } else {
                "recorded pass"
            };
            let responsible = latest
                .iter()
                .filter(|r| match state {
                    "stale" => r.check != check || r.before != current,
                    "recorded failure" => !r.succeeded(),
                    _ => true,
                })
                .min_by_key(|r| &r.digest);
            Ok(Status {
                name,
                state,
                receipt: responsible.map(|r| r.digest.clone()),
            })
        })
        .collect()
}

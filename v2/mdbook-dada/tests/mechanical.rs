//! Mechanical receipts exercise real local fixture commands, never a proof checker.
//! Repacked receipts below are adversarial fixture data, not repository evidence.
#![cfg(unix)]

use mdbook_dada::{
    inventory::hash,
    mechanical::{self, Check, Configuration, Execution},
};
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicUsize, Ordering},
};

struct Fixture(PathBuf);

impl Fixture {
    fn new(script: &str) -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "dada-mechanical-tests-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        let fixture = Self(path.canonicalize().unwrap());
        fixture.write("mdbook-dada/src/lib.rs", "pub fn runner_fixture() {}\n");
        fixture.write("sources/model.txt", "original source\n");
        fixture.configure(Check {
            description: "A local fixture command, not a formal proof check".into(),
            cwd: ".".into(),
            command: vec!["sh".into(), "-c".into(), script.into()],
            version: vec!["sh".into(), "-c".into(), "printf fixture-v1".into()],
            inputs: vec!["sources".into()],
        });
        fixture
    }

    fn write(&self, path: &str, bytes: impl AsRef<[u8]>) {
        let path = self.0.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, bytes).unwrap();
    }

    fn configure(&self, check: Check) {
        let config = Configuration {
            schema: 1,
            checks: BTreeMap::from([("fixture".into(), check)]),
        };
        self.write("spec-checks.json", serde_json::to_vec(&config).unwrap());
    }

    fn check(&self) -> Check {
        Configuration::load(&self.0).unwrap().checks["fixture"].clone()
    }

    fn run(&self) -> (PathBuf, Execution) {
        let path = mechanical::run(&self.0, "fixture").unwrap();
        let receipt = mechanical::load(&path).unwrap();
        (path, receipt)
    }

    fn state(&self) -> &'static str {
        mechanical::status(&self.0).unwrap()[0].state
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

fn repack(receipt: &mut Execution) {
    receipt.digest.clear();
    receipt.digest = hash(&serde_json::to_vec(receipt).unwrap());
}

fn save_repacked(root: &Path, mut receipt: Execution) -> PathBuf {
    repack(&mut receipt);
    let path = root
        .join("evidence/executions")
        .join(format!("{}.json", receipt.digest));
    fs::write(&path, serde_json::to_vec(&receipt).unwrap()).unwrap();
    path
}

#[test]
fn execution_preserves_success_failure_and_non_utf8_output() {
    let successful = Fixture::new("printf done; printf diagnostic >&2");
    let (_, receipt) = successful.run();
    assert!(receipt.succeeded());
    let output = receipt.command.unwrap();
    assert_eq!(output.stdout, b"done");
    assert_eq!(output.stderr, b"diagnostic");
    assert_eq!(output.exit_code, Some(0));
    assert_eq!(successful.state(), "recorded pass");

    let failing = Fixture::new("printf '\\377\\000ok'; printf '\\376err' >&2; exit 7");
    let (path, receipt) = failing.run();
    assert!(path.is_file(), "failure must leave an inspectable receipt");
    assert!(!receipt.succeeded());
    let output = receipt.command.unwrap();
    assert_eq!(output.stdout, [255, 0, b'o', b'k']);
    assert_eq!(output.stderr, [254, b'e', b'r', b'r']);
    assert_eq!(output.exit_code, Some(7));
    assert_eq!(failing.state(), "recorded failure");
}

#[test]
fn execution_retains_source_mutations_additions_and_deletions() {
    for script in [
        "printf changed > sources/model.txt",
        "printf added > sources/added.txt",
        "rm sources/model.txt",
    ] {
        let fixture = Fixture::new(script);
        let (_, receipt) = fixture.run();
        assert_eq!(receipt.command.as_ref().unwrap().exit_code, Some(0));
        assert!(!receipt.succeeded(), "input changes escaped: {script}");
        assert_ne!(receipt.after.as_ref(), Some(&receipt.before));
        assert_eq!(fixture.state(), "stale");
    }
}

#[test]
fn failed_after_snapshot_and_launch_failures_are_retained() {
    let deleted = Fixture::new("rm sources/model.txt");
    let mut check = deleted.check();
    check.inputs = vec!["sources/model.txt".into()];
    deleted.configure(check);
    let (_, receipt) = deleted.run();
    assert!(receipt.after.is_none());
    assert!(receipt.after_error.is_some());
    assert!(!receipt.succeeded());
    assert_eq!(mechanical::records(&deleted.0).unwrap().len(), 1);

    let missing_command = Fixture::new("exit 0");
    let mut check = missing_command.check();
    check.command = vec![missing_command
        .0
        .join("absent-program")
        .display()
        .to_string()];
    missing_command.configure(check);
    let (_, receipt) = missing_command.run();
    assert!(receipt.command.unwrap().launch_error.is_some());
    assert_eq!(missing_command.state(), "recorded failure");

    let failed_version = Fixture::new("touch should-not-run");
    let mut check = failed_version.check();
    check.version = vec!["sh".into(), "-c".into(), "exit 3".into()];
    failed_version.configure(check);
    let (_, receipt) = failed_version.run();
    assert!(receipt.command.is_none());
    assert_eq!(receipt.version_before.exit_code, Some(3));
    assert!(!failed_version.0.join("should-not-run").exists());
}

#[test]
fn status_and_record_validation_never_execute_profile_commands() {
    let fixture = Fixture::new("printf called >> invocations");
    assert_eq!(fixture.state(), "not recorded");
    assert!(!fixture.0.join("invocations").exists());
    fixture.run();
    for _ in 0..3 {
        assert_eq!(fixture.state(), "recorded pass");
        assert_eq!(mechanical::records(&fixture.0).unwrap().len(), 1);
    }
    assert_eq!(fs::read(fixture.0.join("invocations")).unwrap(), b"called");
}

#[test]
fn source_or_profile_changes_stale_receipts_without_corrupting_history() {
    let fixture = Fixture::new("exit 0");
    let (path, _) = fixture.run();
    fixture.write("sources/model.txt", "changed\n");
    assert_eq!(fixture.state(), "stale");
    assert!(mechanical::load(&path).unwrap().succeeded());
    fixture.write("sources/model.txt", "original source\n");
    let mut check = fixture.check();
    check.description.push_str(" with revised scope");
    fixture.configure(check);
    assert_eq!(fixture.state(), "stale");
    assert_eq!(mechanical::records(&fixture.0).unwrap().len(), 1);
}

#[test]
fn later_failures_and_tied_failures_cannot_be_hidden_by_success() {
    let fixture = Fixture::new("if test -f fail-now; then exit 8; fi");
    let (pass_path, mut passed) = fixture.run();
    fixture.write("fail-now", "");
    let (fail_path, mut failed) = fixture.run();
    fs::remove_file(pass_path).unwrap();
    fs::remove_file(fail_path).unwrap();

    // Give the failed fixture receipt a strictly later timestamp first.
    failed.finished_unix_ms = passed.finished_unix_ms + 1;
    failed.started_unix_ms = passed.started_unix_ms;
    let fail_path = save_repacked(&fixture.0, failed.clone());
    let pass_path = save_repacked(&fixture.0, passed.clone());
    assert_eq!(fixture.state(), "recorded failure");
    fs::remove_file(pass_path).unwrap();
    fs::remove_file(fail_path).unwrap();

    // Timestamps are not unique. Choose a success digest that sorts after the
    // failure, so digest tie-breaking cannot accidentally hide that failure.
    passed.finished_unix_ms = failed.finished_unix_ms;
    repack(&mut failed);
    for nonce in 0..10_000 {
        passed.host_os = format!("synthetic-test-host-{nonce}");
        repack(&mut passed);
        if passed.digest > failed.digest {
            break;
        }
    }
    assert!(passed.digest > failed.digest);
    let failed_digest = failed.digest.clone();
    save_repacked(&fixture.0, passed);
    save_repacked(&fixture.0, failed);
    assert_eq!(fixture.state(), "recorded failure");
    assert_eq!(
        mechanical::status(&fixture.0).unwrap()[0].receipt,
        Some(failed_digest),
        "a failure status must identify the failing receipt"
    );
}

#[test]
fn changed_tool_versions_prevent_recorded_success() {
    let fixture = Fixture::new("touch version-changed");
    let mut check = fixture.check();
    check.version = vec![
        "sh".into(),
        "-c".into(),
        "if test -f version-changed; then printf version-2; else printf version-1; fi".into(),
    ];
    fixture.configure(check);
    let (_, receipt) = fixture.run();
    assert_eq!(receipt.command.as_ref().unwrap().exit_code, Some(0));
    assert_eq!(receipt.before, receipt.after.as_ref().unwrap().clone());
    assert_ne!(receipt.version_before, receipt.version_after);
    assert!(!receipt.succeeded());
    assert_eq!(fixture.state(), "recorded failure");
}

#[test]
fn command_arguments_are_literal_and_working_directory_is_recorded() {
    let fixture = Fixture::new("exit 0");
    fs::create_dir(fixture.0.join("sources/work")).unwrap();
    let mut check = fixture.check();
    check.cwd = "sources/work".into();
    check.command = vec!["/bin/echo".into(), "$(touch unintended); literal".into()];
    fixture.configure(check);
    let (_, receipt) = fixture.run();
    assert!(receipt.succeeded());
    assert_eq!(receipt.check.cwd, "sources/work");
    assert_eq!(
        receipt.command.unwrap().stdout,
        b"$(touch unintended); literal\n"
    );
    assert!(!fixture.0.join("sources/work/unintended").exists());
}

#[test]
fn receipt_validation_rejects_tampering_and_profile_substitution() {
    let fixture = Fixture::new("exit 0");
    let (path, receipt) = fixture.run();
    let mut tampered = receipt.clone();
    tampered.command.as_mut().unwrap().stdout.push(42);
    fs::write(&path, serde_json::to_vec(&tampered).unwrap()).unwrap();
    assert!(mechanical::load(&path).is_err());
    fs::remove_file(path).unwrap();

    let mut substituted = receipt;
    substituted.check.command = vec!["made-up-check".into()];
    let path = save_repacked(&fixture.0, substituted);
    assert!(
        mechanical::load(&path).is_err(),
        "embedded check must agree with snapshotted configuration"
    );
}

#[test]
fn receipt_validation_requires_selected_sources_and_runner_snapshots() {
    let fixture = Fixture::new("exit 0");
    let (original_path, receipt) = fixture.run();
    fs::remove_file(original_path).unwrap();
    for missing in [
        "sources/model.txt",
        "mdbook-dada/src/lib.rs",
        "spec-checks.json",
    ] {
        let mut reduced = receipt.clone();
        reduced.before.retain(|input| input.path != missing);
        reduced
            .after
            .as_mut()
            .unwrap()
            .retain(|input| input.path != missing);
        let path = save_repacked(&fixture.0, reduced);
        assert!(
            mechanical::load(&path).is_err(),
            "a self-consistently rehashed missing input escaped: {missing}"
        );
        fs::remove_file(path).unwrap();
    }
}

#[test]
fn snapshots_record_empty_directories_and_ignore_generated_outputs() {
    let fixture = Fixture::new("exit 0");
    fs::create_dir(fixture.0.join("sources/empty")).unwrap();
    let original = mechanical::snapshot(&fixture.0, &fixture.check()).unwrap();
    assert!(original
        .iter()
        .any(|input| input.key == "directory:sources/empty"));
    for output in [
        "sources/.lake/cache",
        "sources/target/debug/output",
        "sources/book/page.html",
        "sources/evidence/record.json",
    ] {
        fixture.write(output, "generated");
    }
    assert_eq!(
        original,
        mechanical::snapshot(&fixture.0, &fixture.check()).unwrap()
    );
    let mut check = fixture.check();
    check.inputs = vec!["sources/target".into()];
    assert!(mechanical::snapshot(&fixture.0, &check).is_err());
}

#[test]
fn snapshots_and_records_reject_symbolic_links() {
    use std::os::unix::fs::symlink;

    let fixture = Fixture::new("exit 0");
    symlink("model.txt", fixture.0.join("sources/alias.txt")).unwrap();
    assert!(mechanical::snapshot(&fixture.0, &fixture.check()).is_err());
    let mut selected_link = fixture.check();
    selected_link.inputs = vec!["sources/alias.txt".into()];
    assert!(mechanical::snapshot(&fixture.0, &selected_link).is_err());
    fs::remove_file(fixture.0.join("sources/alias.txt")).unwrap();
    let (path, _) = fixture.run();
    symlink(path, fixture.0.join("evidence/executions/alias.json")).unwrap();
    assert!(mechanical::records(&fixture.0).is_err());
}

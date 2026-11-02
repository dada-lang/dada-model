use anyhow::{bail, ensure, Result};
use mdbook_dada::{
    evidence::{self, ReviewBundle},
    inventory::{find_root, Inventory},
    link_audit,
    links::{LinkInventory, LinkTarget},
    mechanical,
};
use std::path::Path;

fn run() -> Result<bool> {
    let mut args = std::env::args().skip(1);
    let command = args.next().unwrap_or_else(|| "status".into());
    let root = find_root(&std::env::current_dir()?)?;
    // Mechanical recording is independent of the Markdown inventory, so failed
    // builds and malformed specifications can still have their output retained.
    if command == "run-check" {
        let rest: Vec<_> = args.collect();
        ensure!(rest.len() == 1, "usage: dada-spec run-check <check-name>");
        let path = mechanical::run(&root, &rest[0])?;
        let receipt = mechanical::load(&path)?;
        println!("{}", path.display());
        for outcome in [&receipt.version_before, &receipt.version_after]
            .into_iter()
            .chain(receipt.command.iter())
        {
            if let Some(error) = &outcome.launch_error {
                eprintln!("{error}");
            }
        }
        if let Some(outcome) = &receipt.command {
            use std::io::Write;
            std::io::stdout().write_all(&outcome.stdout)?;
            std::io::stderr().write_all(&outcome.stderr)?;
        }
        if let Some(error) = &receipt.after_error {
            eprintln!("input recapture: {error}");
        }
        println!(
            "Recorded {}. This is not a correspondence decision.",
            if receipt.succeeded() {
                "pass"
            } else {
                "failure or changed inputs"
            }
        );
        return Ok(receipt.succeeded());
    }
    if command == "mechanical-status" {
        ensure!(args.next().is_none(), "usage: dada-spec mechanical-status");
        let statuses = mechanical::status(&root)?;
        for status in &statuses {
            println!(
                "{}: {} ({})",
                status.name,
                status.state,
                status.receipt.as_deref().unwrap_or("no receipt")
            );
        }
        return Ok(statuses.iter().all(|s| s.state == "recorded pass"));
    }
    let inventory = Inventory::load(&root)?;
    match command.as_str() {
        "links" => {
            let rest: Vec<_> = args.collect();
            ensure!(rest.is_empty() || rest == ["--json"], "usage: dada-spec links [--json]");
            let links = LinkInventory::build(&inventory)?;
            let subjects = link_audit::subjects(&inventory)?;
            if rest == ["--json"] {
                println!("{}", serde_json::to_string_pretty(&serde_json::json!({
                    "links": links, "audit_subjects": subjects,
                }))?);
            } else {
                for source in links.sources.values() {
                    println!("{}: {} links{}", source.unit_id, source.occurrences.len(),
                        if source.unit_kind == mdbook_dada::units::UnitKind::FutureNote {
                            " (future note; editorial audits only)"
                        } else { "" });
                    for occurrence in &source.occurrences {
                        let target = match &occurrence.target {
                            LinkTarget::Internal { target } => &target.key,
                            LinkTarget::External { url } => url,
                            LinkTarget::Asset { path } => path,
                        };
                        println!("  {}:{} {:?} {} -> {}", occurrence.source.path,
                            occurrence.source.line, occurrence.direction, occurrence.id, target);
                    }
                }
                for cycle in &links.cycles {
                    println!("Candidate reference cycle: {}", cycle.join(" -> "));
                }
                println!("Required audit subjects (prepare each with dada-spec prepare):");
                for subject in subjects { println!("  {subject}"); }
            }
            Ok(true)
        }
        "check" | "status" => {
            let rest: Vec<_> = args.collect();
            ensure!(rest.is_empty() || rest == ["--explain"], "usage: dada-spec {command} [--explain]");
            let report = evidence::check(&inventory)?;
            for status in &report.statuses {
                println!("{}: inputs={}, correspondence={}", status.unit, status.evidence, status.correspondence);
            }
            for status in mechanical::status(&root)? {
                println!("check {}: {}", status.name, status.state);
            }
            if !report.is_ok() { eprint!("{}", report.render(&inventory)); }
            Ok(report.is_ok())
        }
        "prepare" => {
            let id = args.next().ok_or_else(|| anyhow::anyhow!("usage: dada-spec prepare <unit-id> [--input <file>]..."))?;
            let mut extras = Vec::new();
            while let Some(option) = args.next() {
                ensure!(option == "--input", "unknown prepare option {option}");
                extras.push(args.next().ok_or_else(|| anyhow::anyhow!("--input requires a project-relative file"))?);
            }
            let bundle = ReviewBundle::prepare(&inventory, &id, &extras)?;
            let path = evidence::save_bundle(&inventory, &bundle)?;
            println!("{}", path.display());
            println!("Prepared {} inputs. No review has been recorded. Follow md/repo/correspondence-review.md.", bundle.inputs.len());
            Ok(true)
        }
        "record" => {
            let rest: Vec<_> = args.collect();
            ensure!(rest.len() == 2, "usage: dada-spec record <bundle.json> <review.json>");
            let bundle = evidence::load_bundle(Path::new(&rest[0]))?;
            let review = evidence::load_review(Path::new(&rest[1]))?;
            println!("{}", evidence::record(&inventory, &bundle, &review)?.display());
            Ok(true)
        }
        _ => bail!("usage: dada-spec check | status [--explain] | links [--json] | prepare <subject-id> [--input <file>]... | record <bundle.json> <review.json> | run-check <check-name> | mechanical-status"),
    }
}

fn main() {
    match run() {
        Ok(true) => {}
        Ok(false) => std::process::exit(1),
        Err(error) => {
            eprintln!("{}", evidence::format_error(&error));
            std::process::exit(1);
        }
    }
}

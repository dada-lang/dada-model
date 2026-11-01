use anyhow::{bail, ensure, Result};
use mdbook_dada::{
    evidence::{self, ReviewBundle},
    inventory::{find_root, Inventory},
};
use std::path::Path;

fn run() -> Result<bool> {
    let mut args = std::env::args().skip(1);
    let command = args.next().unwrap_or_else(|| "status".into());
    let root = find_root(&std::env::current_dir()?)?;
    let inventory = Inventory::load(&root)?;
    match command.as_str() {
        "check" | "status" => {
            let rest: Vec<_> = args.collect();
            ensure!(rest.is_empty() || rest == ["--explain"], "usage: dada-spec {command} [--explain]");
            let report = evidence::check(&inventory)?;
            for status in &report.statuses {
                println!("{}: inputs={}, correspondence={}, mechanical={}", status.unit, status.evidence, status.correspondence, status.mechanical);
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
        _ => bail!("usage: dada-spec check | status [--explain] | prepare <unit-id> [--input <file>]... | record <bundle.json> <review.json>"),
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

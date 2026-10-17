use anyhow::{ensure, Result};
use std::io;

fn main() -> Result<()> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.first().is_some_and(|a| a == "supports") {
        std::process::exit(if args.get(1).is_some_and(|a| a == "html") {
            0
        } else {
            1
        });
    }
    ensure!(args.is_empty(), "usage: mdbook-dada [supports html]");
    let (context, mut book): (serde_json::Value, serde_json::Value) =
        serde_json::from_reader(io::stdin())?;
    ensure!(
        context["renderer"] == "html",
        "only the HTML renderer is supported"
    );
    let lean_root = context["config"]["preprocessor"]["dada"]["lean-source"]
        .as_str()
        .map(|p| std::path::Path::new(context["root"].as_str().unwrap_or(".")).join(p));
    mdbook_dada::process_with_lean(&mut book, lean_root.as_deref())?;
    serde_json::to_writer(io::stdout(), &book)?;
    Ok(())
}

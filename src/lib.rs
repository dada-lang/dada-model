use std::sync::Arc;

use clap::Parser;
use dada_lang::FormalityLang;
use fn_error_context::context;
use formality_core::Fallible;
use grammar::Program;

mod grammar;
mod type_system;

formality_core::declare_language! {
    mod dada_lang {
        const NAME = "Dada";
        type Kind = crate::grammar::Kind;
        type Parameter = crate::grammar::Parameter;
        const BINDING_OPEN = '[';
        const BINDING_CLOSE = ']';
        const KEYWORDS = [
            "async",
            "atomic",
            "await",
            "break",
            "class",
            "else",
            "fn",
            "given",
            "if",
            "Int",
            "leased",
            "let",
            "loop",
            "my",
            "our",
            "shared",
            "struct",
            "self",
        ];
    }
}

#[derive(Parser, Debug)] // requires `derive` feature
#[command(author, version, about, long_about = None)]
struct Args {
    paths: Vec<String>,
}

pub fn main() -> Fallible<()> {
    let args = Args::try_parse()?;

    for path in &args.paths {
        check_file(path)?;
    }

    Ok(())
}

#[context("check input file `{path:?}`")]
fn check_file(path: &str) -> Fallible<()> {
    let text: String = std::fs::read_to_string(path)?;
    let program: Arc<Program> = dada_lang::try_term(&text)?;
    type_system::check_program(&program)?;
    Ok(())
}

use dada_lang::FormalityLang;
use formality_core::Fallible;

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
            "class",
            "struct",
            "my",
            "shared",
            "leased",
            "await",
            "async",
            "fn",
            "atomic",
            "break",
            "loop",
            "if",
            "else",
            "let",
        ];
    }
}

pub fn main() -> Fallible<()> {
    Ok(())
}

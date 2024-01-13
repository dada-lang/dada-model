use formality_core::parse::{CoreParse, ParseResult, Parser, Scope};

use crate::dada_lang::FormalityLang;

use super::{LocalVariableDecl, MethodDeclBoundData, ThisDecl, Ty};

impl CoreParse<FormalityLang> for MethodDeclBoundData {
    fn parse<'t>(scope: &Scope<FormalityLang>, text: &'t str) -> ParseResult<'t, Self> {
        Parser::single_variant(scope, text, "MethodDeclBoundData", |parser| {
            parser.expect_char('(')?;
            let this: ThisDecl = parser.nonterminal()?;
            let inputs: Vec<LocalVariableDecl> = if parser.expect_char(',').is_ok() {
                parser.comma_nonterminal()?
            } else {
                vec![]
            };
            parser.expect_char(')')?;

            let output: Ty = if parser.expect_char('-').is_ok() {
                parser.expect_char('>')?;
                parser.nonterminal()?
            } else {
                Ty::unit()
            };

            let body = parser.nonterminal()?;

            Ok(MethodDeclBoundData {
                this,
                inputs,
                output,
                body,
            })
        })
    }
}

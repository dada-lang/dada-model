use std::fmt::{self, Debug};

use formality_core::parse::{CoreParse, ParseResult, Parser, Scope};

use crate::dada_lang::FormalityLang;

use super::{LocalVariableDecl, MethodDeclBoundData, Predicate, ThisDecl, Ty};

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

            let output: Ty = if parser.expect_char('→').is_ok() {
                parser.nonterminal()?
            } else {
                Ty::unit()
            };

            let predicates: Vec<Predicate> = if let Ok(()) = parser.expect_keyword("where") {
                parser.comma_nonterminal()?
            } else {
                Default::default()
            };

            let body = parser.nonterminal()?;

            Ok(MethodDeclBoundData {
                this,
                inputs,
                output,
                predicates,
                body,
            })
        })
    }
}

impl Debug for MethodDeclBoundData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            return f
                .debug_struct("MethodDeclBoundData")
                .field("this", &self.this)
                .field("inputs", &self.inputs)
                .field("output", &self.output)
                .field("predicates", &self.predicates)
                .field("body", &self.body)
                .finish();
        }
        write!(f, "({:?}", self.this)?;
        // Preserve the existing diagnostic layout; source::program supplies the
        // explicit comma after the receiver when rendering parsable source.
        for (index, input) in self.inputs.iter().enumerate() {
            write!(f, "{}{:?}", if index == 0 { " " } else { ", " }, input)?;
        }
        write!(f, ") → {:?}", self.output)?;
        for (index, predicate) in self.predicates.iter().enumerate() {
            write!(
                f,
                "{}{:?}",
                if index == 0 { " where " } else { ", " },
                predicate
            )?;
        }
        write!(f, " {:?}", self.body)
    }
}

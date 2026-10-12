use formality_core::parse::{skip_whitespace, CoreParse, ParseResult, Parser, Scope};

use crate::dada_lang::FormalityLang;

use super::{ParameterTy, ReceiverPermission};

fn starts_keyword(text: &str, keyword: &str) -> bool {
    skip_whitespace(text)
        .strip_prefix(keyword)
        .is_some_and(|rest| {
            rest.chars()
                .next()
                .is_none_or(|ch| !ch.is_ascii_alphanumeric() && ch != '_')
        })
}

fn starts_bare_mutable(text: &str) -> bool {
    let text = skip_whitespace(text);
    text.strip_prefix('!')
        .is_some_and(|rest| !skip_whitespace(rest).starts_with('['))
}

impl CoreParse<FormalityLang> for ParameterTy {
    fn parse<'t>(scope: &Scope<FormalityLang>, text: &'t str) -> ParseResult<'t, Self> {
        Parser::single_variant(scope, text, "parameter type", |p| {
            if super::inline_type_impls::starts_inline_type(scope, p.text()) {
                p.expect_keyword("type")?;
                Ok(Self::inline_ty(super::Ty::var(
                    p.variable_of_kind(super::Kind::Ty)?,
                )))
            } else if starts_keyword(p.text(), "any") {
                p.expect_keyword("any")?;
                Ok(Self::Any(p.nonterminal()?))
            } else if starts_bare_mutable(p.text()) {
                p.expect_char('!')?;
                Ok(Self::Mutable(p.nonterminal()?))
            } else {
                Ok(Self::Explicit(p.nonterminal()?))
            }
        })
    }
}

impl CoreParse<FormalityLang> for ReceiverPermission {
    fn parse<'t>(scope: &Scope<FormalityLang>, text: &'t str) -> ParseResult<'t, Self> {
        Parser::single_variant(scope, text, "receiver permission", |p| {
            Ok(Self::explicit(p.nonterminal::<super::Perm>()?))
        })
    }
}

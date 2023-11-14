use std::sync::Arc;

use formality_core::parse::{CoreParse, Parser, Precedence};
use formality_core::Upcast;

use crate::dada_lang::FormalityLang;

use super::{ClassName, ClassTy, Perm, Ty};

// Customized parse of ty to accept tuples like `()` or `(a, b)` etc.
impl CoreParse<FormalityLang> for Ty {
    fn parse<'t>(
        scope: &formality_core::parse::Scope<FormalityLang>,
        text: &'t str,
    ) -> formality_core::parse::ParseResult<'t, Self> {
        Parser::multi_variant(scope, text, "type", |p| {
            p.parse_variant("variable", Precedence::default(), |p| {
                let ty: Ty = p.variable()?;
                Ok(ty)
            });

            p.parse_variant("tuple", Precedence::default(), |p| {
                p.expect_char('(')?;
                let types: Vec<Ty> = p.comma_nonterminal()?;
                p.expect_char(')')?;
                let name = ClassName::Tuple(types.len());
                Ok(ClassTy::new(name, types).upcast())
            });

            p.parse_variant("class", Precedence::default(), |p| {
                p.mark_as_cast_variant();
                p.reject_variable()?;
                let c: ClassTy = p.nonterminal()?;
                Ok(c.upcast())
            });

            p.parse_variant("perm", Precedence::default(), |p| {
                let perm: Perm = p.nonterminal()?;
                let ty: Ty = p.nonterminal()?;
                Ok(Ty::apply_perm(perm, Arc::new(ty)))
            });
        })
    }
}

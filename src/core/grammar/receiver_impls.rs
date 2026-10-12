use std::fmt::{self, Debug};

use formality_core::parse::{CoreParse, ParseError, ParseResult, Parser, Scope};

use crate::dada_lang::FormalityLang;

use super::{Perm, ThisDecl};

impl CoreParse<FormalityLang> for ThisDecl {
    fn parse<'t>(scope: &Scope<FormalityLang>, text: &'t str) -> ParseResult<'t, Self> {
        Parser::single_variant(scope, text, "core receiver", |p| {
            let mut suffix = p.clone();
            if suffix.expect_keyword("self").is_ok() {
                suffix.expect_char('-')?;
                suffix.expect_char('>')?;
                *p = suffix;
                return Ok(Self::new(Perm::Given));
            }

            let permission: Perm = p.nonterminal()?;
            if permission == Perm::Given {
                return Err(ParseError::at(
                    text,
                    "independently owned receivers must be written `self->`".into(),
                ));
            }
            p.expect_keyword("self")?;
            Ok(Self::new(permission))
        })
    }
}

impl Debug for ThisDecl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            f.debug_struct("ThisDecl")
                .field("perm", &self.perm)
                .finish()
        } else if self.perm == Perm::Given {
            write!(f, "self->")
        } else {
            write!(f, "{:?} self", self.perm)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dada_lang::{term, try_term};

    #[test]
    fn owned_receiver_uses_postfix_arrow() {
        for source in ["self->", "self ->", "self // receiver\n - // arrow\n >"] {
            assert_eq!(term::<ThisDecl>(source), ThisDecl::new(Perm::Given));
        }
        assert_eq!(format!("{:?}", ThisDecl::new(Perm::Given)), "self->");
    }

    #[test]
    fn owned_receiver_uses_postfix_arrow_in_call_diagnostics() {
        let method = term::<super::super::MethodDecl>("fn target[perm P](self->, x: P Data) ...;");
        let error = method.instantiate_for_call(&[]).unwrap_err().to_string();
        assert!(error.contains("(self->, x:"), "{error}");
        assert!(!error.contains("given self"), "{error}");
    }

    #[test]
    fn core_receiver_keeps_explicit_origin_permissions() {
        for permission in [
            "shared",
            "shared[]",
            "shared[x]",
            "![x]",
            "given[x]",
            "given[x] ![y]",
        ] {
            let source = format!("{permission} self");
            assert_eq!(term::<ThisDecl>(&source).perm, term::<Perm>(permission));
        }
    }

    #[test]
    fn core_receiver_rejects_surface_sugar_and_retired_prefixes() {
        for source in [
            "self",
            "self!",
            "any self",
            "!self",
            "given self",
            "given[] self",
            "given [ ] self",
            "^self",
            "self^",
            "self->!",
            "self!->",
        ] {
            assert!(try_term::<ThisDecl>(source).is_err(), "accepted {source}");
        }
    }
}

use std::fmt::{self, Debug};

use formality_core::parse::{CoreParse, ParseError, ParseResult, Parser, Scope};

use crate::dada_lang::FormalityLang;

use super::{Perm, ReceiverPermission, ThisDecl};

impl CoreParse<FormalityLang> for ThisDecl {
    fn parse<'t>(scope: &Scope<FormalityLang>, text: &'t str) -> ParseResult<'t, Self> {
        Parser::single_variant(scope, text, "surface receiver", |p| {
            let mut suffix = p.clone();
            if suffix.expect_keyword("self").is_ok() {
                let mut mutable = suffix.clone();
                if mutable.expect_char('!').is_ok() {
                    *p = mutable;
                    return Ok(Self::new(ReceiverPermission::Mutable));
                }

                let mut given = suffix.clone();
                if given.expect_char('-').is_ok() {
                    given.expect_char('>')?;
                    *p = given;
                    return Ok(Self::new(Perm::Given));
                }

                *p = suffix;
                return Ok(Self::new(ReceiverPermission::Any));
            }

            let permission: ReceiverPermission = p.nonterminal()?;
            if permission == ReceiverPermission::explicit(Perm::Given) {
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
            return f
                .debug_struct("ThisDecl")
                .field("perm", &self.perm)
                .finish();
        }
        match &self.perm {
            ReceiverPermission::Any => write!(f, "self"),
            ReceiverPermission::Mutable => write!(f, "self!"),
            ReceiverPermission::Explicit(Perm::Given) => write!(f, "self->"),
            ReceiverPermission::Explicit(permission) => write!(f, "{permission:?} self"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::grammar as core;
    use crate::dada_lang::{term, try_term};

    #[test]
    fn surface_receiver_suffixes_parse_with_whitespace_and_comments() {
        for source in ["self!", "self !", "self // receiver\n !"] {
            assert_eq!(term::<ThisDecl>(source).perm, ReceiverPermission::Mutable);
        }
        for source in ["self->", "self ->", "self // receiver\n - // arrow\n >"] {
            assert_eq!(
                term::<ThisDecl>(source).perm,
                ReceiverPermission::explicit(Perm::Given)
            );
        }
        for source in ["self", "any self", "any // permission\n self"] {
            assert_eq!(term::<ThisDecl>(source).perm, ReceiverPermission::Any);
        }
        assert_eq!(format!("{:?}", term::<ThisDecl>("self!")), "self!");
        assert_eq!(format!("{:?}", term::<ThisDecl>("self->")), "self->");
    }

    #[test]
    fn surface_receiver_keeps_explicit_origin_permissions() {
        for permission in [
            "shared",
            "shared[]",
            "shared[x]",
            "![x]",
            "given[x]",
            "given[x] ![y]",
        ] {
            let source = format!("{permission} // prefix\n self");
            assert_eq!(
                term::<ThisDecl>(&source).perm,
                ReceiverPermission::explicit(term::<Perm>(permission))
            );
        }
    }

    #[test]
    fn surface_receiver_rejects_retired_prefixes_and_combined_suffixes() {
        for source in [
            "!self",
            "! self",
            "given self",
            "given[] self",
            "given [ ] self",
            "^self",
            "self^",
            "self->!",
            "self!->",
            "self!!",
            "any self!",
            "shared self->",
            "given[x] self!",
        ] {
            assert!(try_term::<ThisDecl>(source).is_err(), "accepted {source}");
        }
    }

    #[test]
    fn suffix_receiver_sugar_preserves_generated_permission_order() {
        crate::assert_desugars!({
            struct Container[ty T] where T is struct {
                fn method[perm P](self!, x: any T, y: !T, z: P T)
                    where P is owned ...;
                fn generic[perm P](P self, x: P T) ...;
                fn consume(self->, x: given T) ...;
                fn defaulted(self, x: T) ...;
                fn any_receiver(any self) ...;
            }
        } => {
            struct Container[ty T] where T is struct {
                fn method[perm P, perm Receiver, perm Input, perm Mutable](Receiver self, x: Input T, y: Mutable T, z: P T)
                    where P is owned, Receiver is mut, Mutable is mut ...;
                fn generic[perm P](P self, x: P T) ...;
                fn consume(self->, x: given T) ...;
                fn defaulted[perm Receiver, perm Input](Receiver self, x: Input T) ...;
                fn any_receiver[perm Receiver](Receiver self) ...;
            }
        });
    }

    #[test]
    fn owned_receiver_renderer_roundtrips_through_surface() {
        let original =
            crate::surface::parse_program("struct Data { fn method(self->) {} }").unwrap();
        let rendered = core::source::program(&original).unwrap();
        assert!(rendered.contains("fn method(self->)"), "{rendered}");
        assert!(!rendered.contains("given self"), "{rendered}");
        assert_eq!(
            *crate::surface::parse_program(&rendered).unwrap(),
            *original
        );
    }
}

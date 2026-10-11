use super::{Access, PlaceExpr};
use crate::dada_lang::FormalityLang;
use formality_core::parse::{CoreParse, ParseResult, Parser, Scope};
use std::fmt::{self, Debug};

impl CoreParse<FormalityLang> for PlaceExpr {
    fn parse<'t>(scope: &Scope<FormalityLang>, text: &'t str) -> ParseResult<'t, Self> {
        Parser::single_variant(scope, text, "PlaceExpr", |p| {
            let place = p.nonterminal()?;
            let mut suffix = p.clone();
            let access = if suffix.expect_char('^').is_ok() {
                *p = suffix;
                Access::Gv
            } else {
                let mut suffix = p.clone();
                if suffix.expect_char('!').is_ok() {
                    // `!=` is a binary operator, not a mutable access followed by `=`.
                    let mut comparison = suffix.clone();
                    if comparison.expect_char('=').is_err() {
                        *p = suffix;
                        Access::Mt
                    } else {
                        Access::SharePlace
                    }
                } else {
                    let mut suffix = p.clone();
                    if suffix.expect_char('.').is_ok() {
                        match suffix.expect_keyword_in(&["share", "drop"]) {
                            Ok(keyword) => {
                                *p = suffix;
                                if keyword == "share" {
                                    Access::SharePlace
                                } else {
                                    Access::Drop
                                }
                            }
                            Err(_) => Access::SharePlace,
                        }
                    } else {
                        Access::SharePlace
                    }
                }
            };
            Ok(PlaceExpr { place, access })
        })
    }
}

impl Debug for PlaceExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            f.debug_struct("PlaceExpr")
                .field("place", &self.place)
                .field("access", &self.access)
                .finish()
        } else {
            write!(f, "{:?} {:?}", self.place, self.access)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::grammar::{BinaryOp, Expr, Place, Statement};
    use crate::dada_lang::{term, try_term};

    #[test]
    fn bare_and_explicit_place_sharing_are_identical() {
        for place in ["x", "x.field", "x[0].field"] {
            let expected = PlaceExpr {
                place: term::<Place>(place),
                access: Access::SharePlace,
            };
            assert_eq!(term::<PlaceExpr>(place), expected);
            assert_eq!(term::<PlaceExpr>(&format!("{place}.share")), expected);
        }
    }

    #[test]
    fn suffix_accesses_apply_to_the_entire_projected_place() {
        for (suffix, access) in [
            ("^", Access::Gv),
            ("!", Access::Mt),
            (".drop", Access::Drop),
        ] {
            let actual = term::<PlaceExpr>(&format!("x.field[0]{suffix}"));
            assert_eq!(actual.place, term::<Place>("x.field[0]"));
            assert_eq!(actual.access, access);
        }
    }

    #[test]
    fn explicit_place_sharing_is_not_value_sharing() {
        assert!(matches!(term::<Expr>("x.share"), Expr::Place(_)));
        for text in ["x^.share", "x.share.share", "new Foo().share"] {
            assert!(matches!(term::<Expr>(text), Expr::ShareValue(_)), "{text}");
        }
        let Expr::ShareValue(value) = term::<Expr>("x^.share") else {
            unreachable!()
        };
        let Expr::Place(place) = value.as_ref() else {
            panic!("expected given place")
        };
        assert_eq!(place.access, Access::Gv);
    }

    #[test]
    fn mutable_suffix_does_not_consume_inequality() {
        let Expr::BinaryOp(left, BinaryOp::Ne, _) = term::<Expr>("x != y") else {
            panic!("expected inequality");
        };
        let Expr::Place(place) = left.as_ref() else {
            panic!("expected place")
        };
        assert_eq!(place.access, Access::SharePlace);
        assert!(matches!(term::<Expr>("!"), Expr::Panic));
        assert_eq!(term::<PlaceExpr>("x!").access, Access::Mt);
        assert!(try_term::<PlaceExpr>("x!!").is_err());
    }

    #[test]
    fn bare_place_receivers_do_not_swallow_method_names() {
        for text in [
            "x.foo()",
            "x.field.foo[^](y)",
            "x.field[0].foo[Array[Int], ^](y^)",
            "x.foo().bar()",
            "x!.foo()",
            "x^.foo()",
            "x.share.foo()",
            "x.foo // comment before generics\n [^] // comment before arguments\n ()",
        ] {
            assert!(matches!(term::<Expr>(text), Expr::Call(..)), "{text}");
        }
        let Expr::Call(receiver, _, _, _) = term::<Expr>("x.field.foo[^](y)") else {
            unreachable!()
        };
        let Expr::Place(receiver) = receiver.as_ref() else {
            panic!("expected place")
        };
        assert_eq!(receiver.place, term::<Place>("x.field"));
        assert_eq!(receiver.access, Access::SharePlace);
    }

    #[test]
    fn assignment_destination_is_still_a_place() {
        let Statement::Reassign(place, _) = term::<Statement>("x.field = y;") else {
            panic!("expected assignment");
        };
        assert_eq!(place, term::<Place>("x.field"));
    }
}

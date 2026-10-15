use formality_core::parse::{CoreParse, ParseError, ParseResult, Parser, Scope};

use super::{Access, PlaceExpr, SigilCallReceiver};
use crate::dada_lang::FormalityLang;

impl CoreParse<FormalityLang> for SigilCallReceiver {
    fn parse<'t>(scope: &Scope<FormalityLang>, text: &'t str) -> ParseResult<'t, Self> {
        Parser::single_variant(scope, text, "SigilCallReceiver", |p| {
            // Cast reductions are ignored when comparing competing parses.
            // Parsing PlaceExpr directly ensures the standalone access remains
            // a prefix of this receiver, rather than an ambiguous alternative.
            p.mark_as_cast_variant();
            let place_expr: PlaceExpr = p.nonterminal()?;
            if !matches!(place_expr.access, Access::Gv | Access::Mt) {
                return Err(ParseError::at(
                    text,
                    "a dotless method receiver requires `→` or `!`".into(),
                ));
            }
            Ok(Self::new(place_expr))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::grammar as core;
    use crate::dada_lang::{term, try_term};
    use crate::surface::{desugar::lower_expr, grammar::Expr};

    fn lowered(source: &str) -> core::Expr {
        lower_expr(term::<Expr>(source)).into_singleton().unwrap().0
    }

    #[test]
    fn dotless_calls_lower_to_their_dotted_forms() {
        for (dotless, dotted) in [
            ("vec→iter()", "vec→.iter()"),
            ("vec!push(value)", "vec!.push(value)"),
            ("self→take()", "self→.take()"),
            ("self!edit()", "self!.edit()"),
            ("vec.field[0]→iter()", "vec.field[0]→.iter()"),
            ("vec.field[0]!push(value!)", "vec.field[0]!.push(value!)"),
            (
                "vec!push[Data, ![vec], shared[value]](value)",
                "vec!.push[Data, ![vec], shared[value]](value)",
            ),
            (
                "vec→iter[Array[[source] Data], [] Data]()",
                "vec→.iter[Array[[source] Data], [] Data]()",
            ),
            ("vec→iter().next()", "vec→.iter().next()"),
            ("vec!push(other→take())", "vec!.push(other→.take())"),
            ("vec→iter().share", "vec→.iter().share"),
        ] {
            assert_eq!(lowered(dotless), lowered(dotted), "{dotless}");
        }
        assert!(matches!(term::<Expr>("vec→iter()"), Expr::SigilCall(..)));
        assert_eq!(
            lowered("vec!push[Data, ![vec]](value!)"),
            term::<core::Expr>("vec!.push[Data, ![vec]](value!)")
        );
    }

    #[test]
    fn standalone_accesses_and_value_sharing_keep_their_meanings() {
        for (source, access) in [("vec→", Access::Gv), ("vec!", Access::Mt)] {
            let Expr::Place(place) = term::<Expr>(source) else {
                panic!("expected standalone access: {source}")
            };
            assert_eq!(place.access, access);
        }
        let Expr::ShareValue(value) = term::<Expr>("vec→.share") else {
            panic!("expected value sharing")
        };
        let Expr::Place(place) = value.as_ref() else {
            panic!("expected moved place")
        };
        assert_eq!(place.access, Access::Gv);
        // A standalone access must still end before the next tuple element.
        assert!(matches!(term::<Expr>("(vec!, other)"), Expr::Tuple(_)));
    }

    #[test]
    fn calls_in_tuples_cannot_be_mistaken_for_separate_core_elements() {
        for (source, dotted) in [
            ("(vec!iter())", "(vec!.iter())"),
            ("(vec! iter())", "(vec!.iter())"),
            ("(vec!iter(),)", "(vec!.iter(),)"),
            ("(vec→iter(),)", "(vec→.iter(),)"),
        ] {
            let actual = lowered(source);
            assert_eq!(actual, term::<core::Expr>(dotted), "{source}");
            assert!(
                matches!(actual, core::Expr::Tuple(elements) if elements.len() == 1),
                "{source}"
            );
            assert!(try_term::<core::Expr>(source).is_err(), "{source}");
        }
    }

    #[test]
    fn dotless_calls_allow_whitespace_and_comments_at_token_boundaries() {
        for (source, expected) in [
            ("vec → iter ()", "vec→.iter()"),
            ("vec // arrow\n → iter()", "vec→.iter()"),
            ("vec ! push (value)", "vec!.push(value)"),
            (
                "vec // before access\n → // before method\n iter // before generics\n [Array[[source] Data]] // before arguments\n ()",
                "vec→.iter[Array[[source] Data]]()",
            ),
            (
                "vec!push[ // ] ignored\n shared[value]] // [ ignored\n(value)",
                "vec!.push[shared[value]](value)",
            ),
        ] {
            assert_eq!(lowered(source), lowered(expected), "{source}");
        }
    }

    #[test]
    fn calls_bind_more_tightly_than_binary_operators() {
        for (source, expected) in [
            ("vec→len() + 1", "vec→.len() + 1"),
            ("1 + vec→len()", "1 + vec→.len()"),
            ("vec→len() - other→len()", "vec→.len() - other→.len()"),
            ("vec!len() != other", "vec!.len() != other"),
            ("vec ! // comment\n = other", "vec != other"),
            ("vec != other→len()", "vec != other→.len()"),
        ] {
            assert_eq!(lowered(source), lowered(expected), "{source}");
        }
        assert!(matches!(
            term::<Expr>("vec - other"),
            Expr::BinaryOp(_, core::BinaryOp::Sub, _)
        ));
        let Expr::BinaryOp(left, core::BinaryOp::Add, right) =
            term::<Expr>("vec→len() + other!len()")
        else {
            panic!("expected addition of two method calls")
        };
        assert!(matches!(left.as_ref(), Expr::SigilCall(..)));
        assert!(matches!(right.as_ref(), Expr::SigilCall(..)));
    }

    #[test]
    fn dotless_calls_require_a_place_access_and_an_ordinary_method_name() {
        for source in [
            "vec iter()",
            "vec.share iter()",
            "vec→iter()→next()",
            "vec→iter()!next()",
            "new Vec()→iter()",
            "(vec→)→iter()",
            "vec→share",
            "vec→share()",
            "vec!share()",
            "vec→.share()",
            "vec→iter",
            "vec→iter[",
            "vec!push[Data](value",
        ] {
            assert!(try_term::<Expr>(source).is_err(), "{source}");
        }
        assert!(try_term::<SigilCallReceiver>("vec!").is_ok());
        assert!(try_term::<SigilCallReceiver>("vec").is_err());
        assert!(try_term::<SigilCallReceiver>("vec.share").is_err());
        assert!(try_term::<core::Expr>("vec→iter()").is_err());
        assert!(try_term::<core::Expr>("vec!push(value)").is_err());
    }
}

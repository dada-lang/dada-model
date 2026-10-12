use std::fmt::{self, Debug};

use formality_core::parse::{CoreParse, ParseResult, Parser, Precedence, Scope};

use super::ReceiverSigil;
use crate::dada_lang::FormalityLang;

// See core's access_impls: Unicode punctuation needs an explicit parser because
// it cannot be represented by the pinned #[grammar] token syntax.
impl CoreParse<FormalityLang> for ReceiverSigil {
    fn parse<'t>(scope: &Scope<FormalityLang>, text: &'t str) -> ParseResult<'t, Self> {
        Parser::multi_variant(scope, text, "ReceiverSigil", |parser| {
            parser.parse_variant("ReceiverSigil::Any", Precedence::default(), |p| {
                p.expect_char('.')?;
                Ok(Self::Any)
            });
            parser.parse_variant("ReceiverSigil::Mutable", Precedence::default(), |p| {
                p.expect_char('!')?;
                Ok(Self::Mutable)
            });
            parser.parse_variant("ReceiverSigil::Given", Precedence::default(), |p| {
                p.expect_char('→')?;
                Ok(Self::Given)
            });
        })
    }
}

impl Debug for ReceiverSigil {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (name, text) = match self {
            Self::Any => ("Any", "."),
            Self::Mutable => ("Mutable", "!"),
            Self::Given => ("Given", "→"),
        };
        if f.alternate() {
            f.debug_tuple(name).finish()
        } else {
            f.write_str(text)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::core::grammar as core;
    use crate::dada_lang::{term, try_term};
    use crate::surface::{
        desugar::lower_expr,
        grammar::{Expr, MethodDecl},
    };

    #[test]
    fn unicode_arrow_core_source_round_trips_through_surface() {
        let program = crate::surface::parse_program(
            "struct Worker { fn self→take(value: given Int) → Int { value→; } } struct Main { fn main(given self) { let worker = new Worker(); print(worker→take(5)); } }",
        ).unwrap();
        let source = core::source::program(&program).unwrap();
        assert!(source.contains("→"), "{source}");
        assert!(!source.contains("->"), "{source}");
        assert_eq!(
            *program,
            *crate::surface::parse_program(&source).unwrap(),
            "{source}"
        );
        assert_eq!(*program, term::<core::Program>(&source), "{source}");
    }

    #[test]
    fn unicode_arrows_lower_receivers_calls_and_returns() {
        crate::assert_desugars!(
            "struct Worker { fn self→take(value: given Int) → Int { value→; } }"
            => "struct Worker { fn take(given self, value: given Int) → Int { value→; } }"
        );
        for (source, expected) in [
            ("x→method[given](y→)", "x→.method[given](y→)"),
            (
                "x // before arrow\n → // after arrow\n method()",
                "x→.method()",
            ),
            ("x.field[0]→method().next()", "x.field[0]→.method().next()"),
            ("x→method() - y→method()", "x→.method() - y→.method()"),
            ("x != y→method()", "x != y→.method()"),
            ("x→method(x!edit())", "x→.method(x!.edit())"),
        ] {
            assert_eq!(
                lower_expr(term::<Expr>(source)).into_singleton().unwrap().0,
                term::<core::Expr>(expected),
                "{source}"
            );
        }
        for source in [
            "fn self→take() → Int ...;",
            "fn self // before arrow\n → // after arrow\n take() // before return\n → // after return\n Int ...;",
            "fn explicit(given self) → Int ...;",
        ] {
            assert!(try_term::<MethodDecl>(source).is_ok(), "{source}");
        }
        for source in [
            "fn self->take() ...;",
            "fn self.take() -> Int ...;",
            "fn explicit(given self) -> Int ...;",
        ] {
            assert!(try_term::<MethodDecl>(source).is_err(), "{source}");
        }
        for source in [
            "x->method()",
            "x→method()->next()",
            "x→share()",
            "x→.share()",
        ] {
            assert!(try_term::<Expr>(source).is_err(), "{source}");
        }
        assert!(try_term::<core::MethodDecl>("fn explicit(given self) → Int ...;").is_ok());
        assert!(try_term::<core::MethodDecl>("fn explicit(given self) -> Int ...;").is_err());
    }
}

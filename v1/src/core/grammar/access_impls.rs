use std::fmt::{self, Debug};

use formality_core::parse::{CoreParse, ParseResult, Parser, Precedence, Scope};

use super::Access;
use crate::dada_lang::FormalityLang;

// Rust's token grammar cannot contain `→`, and the pinned formality macros do
// not accept quoted terminals. Keep this token's parser and formatter explicit.
impl CoreParse<FormalityLang> for Access {
    fn parse<'t>(scope: &Scope<FormalityLang>, text: &'t str) -> ParseResult<'t, Self> {
        Parser::multi_variant(scope, text, "Access", |parser| {
            parser.parse_variant("Access::SharePlace", Precedence::default(), |p| {
                p.expect_char('.')?;
                p.expect_keyword("share")?;
                Ok(Self::SharePlace)
            });
            parser.parse_variant("Access::Gv", Precedence::default(), |p| {
                p.expect_char('→')?;
                Ok(Self::Gv)
            });
            parser.parse_variant("Access::Mt", Precedence::default(), |p| {
                p.expect_char('!')?;
                Ok(Self::Mt)
            });
            parser.parse_variant("Access::Drop", Precedence::default(), |p| {
                p.expect_char('.')?;
                p.expect_keyword("drop")?;
                Ok(Self::Drop)
            });
        })
    }
}

impl Debug for Access {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (name, text) = match self {
            Self::SharePlace => ("SharePlace", ". share"),
            Self::Gv => ("Gv", "→"),
            Self::Mt => ("Mt", "!"),
            Self::Drop => ("Drop", ". drop"),
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
    use super::*;
    use crate::core::grammar::{BinaryOp, Expr, PlaceExpr};
    use crate::dada_lang::{term, try_term};

    #[test]
    fn unicode_arrow_access_parses_and_formats() {
        assert_eq!(term::<Access>("→"), Access::Gv);
        assert_eq!(format!("{:?}", Access::Gv), "→");
        for source in ["x→", "x.field[0]→", "x // before arrow\n → // after arrow"] {
            assert_eq!(term::<PlaceExpr>(source).access, Access::Gv, "{source}");
        }
        for source in ["x->", "x - >", "x - // split\n >", "x→>"] {
            assert!(try_term::<PlaceExpr>(source).is_err(), "{source}");
        }
        for source in ["x - y", "x-1", "x - // comment\n y"] {
            assert!(
                matches!(term::<Expr>(source), Expr::BinaryOp(_, BinaryOp::Sub, _)),
                "{source}"
            );
        }
        assert!(matches!(term::<Expr>("x→.share"), Expr::ShareValue(_)));
        assert!(matches!(
            term::<Expr>("x→.method[given](y→)"),
            Expr::Call(..)
        ));
        assert!(try_term::<Expr>("x→method()").is_err());
    }
}

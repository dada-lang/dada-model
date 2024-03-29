use formality_core::parse::{CoreParse, Parser, Precedence};
use std::fmt::Debug;

use crate::dada_lang::FormalityLang;

use super::{NamedTy, Parameter, Ty, TypeName, ValueId};

// Customized parse of ty to accept tuples like `()` or `(a, b)` etc.
impl CoreParse<FormalityLang> for NamedTy {
    fn parse<'t>(
        scope: &formality_core::parse::Scope<FormalityLang>,
        text: &'t str,
    ) -> formality_core::parse::ParseResult<'t, Self> {
        Parser::multi_variant(scope, text, "type", |p| {
            p.parse_variant("tuple", Precedence::default(), |p| {
                p.expect_char('(')?;
                let types: Vec<Ty> = p.comma_nonterminal()?;
                p.expect_char(')')?;
                let name = TypeName::Tuple(types.len());
                Ok(NamedTy::new(name, types))
            });

            p.parse_variant("int", Precedence::default(), |p| {
                p.expect_keyword("Int")?;
                let name = TypeName::Int;
                let parameters: Vec<Parameter> = vec![];
                Ok(NamedTy::new(name, parameters))
            });

            p.parse_variant("class", Precedence::default(), |p| {
                p.mark_as_cast_variant();
                let id: ValueId = p.nonterminal()?;
                let parameters: Vec<Parameter> = p.delimited_nonterminal('[', true, ']')?;
                Ok(NamedTy::new(id, parameters))
            });
        })
    }
}

impl Debug for NamedTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            f.debug_struct("NamedTy")
                .field("name", &self.name)
                .field("parameters", &self.parameters)
                .finish()
        } else {
            match self.name {
                TypeName::Tuple(_) => {
                    write!(f, "(")?;
                    for (p, i) in self.parameters.iter().zip(0..) {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{:?}", p)?;
                    }
                    write!(f, ")")?;
                }

                _ => {
                    write!(f, "{:?}", self.name)?;

                    if self.parameters.len() > 0 {
                        write!(f, "[")?;
                        for (p, i) in self.parameters.iter().zip(0..) {
                            if i > 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{:?}", p)?;
                        }
                        write!(f, "]")?;
                    }
                }
            }
            Ok(())
        }
    }
}

use formality_core::parse::{CoreParse, Parser, Precedence};
use formality_core::Upcast;
use std::fmt::Debug;

use crate::dada_lang::FormalityLang;

use super::{ClassName, ClassTy, Ty};

// Customized parse of ty to accept tuples like `()` or `(a, b)` etc.
impl CoreParse<FormalityLang> for ClassTy {
    fn parse<'t>(
        scope: &formality_core::parse::Scope<FormalityLang>,
        text: &'t str,
    ) -> formality_core::parse::ParseResult<'t, Self> {
        Parser::multi_variant(scope, text, "type", |p| {
            p.parse_variant("tuple", Precedence::default(), |p| {
                p.expect_char('(')?;
                let types: Vec<Ty> = p.comma_nonterminal()?;
                p.expect_char(')')?;
                let name = ClassName::Tuple(types.len());
                Ok(ClassTy::new(name, types))
            });

            p.parse_variant("class", Precedence::default(), |p| {
                p.mark_as_cast_variant();
                p.reject_variable()?;
                let c: ClassTy = p.nonterminal()?;
                Ok(c)
            });
        })
    }
}

impl Debug for ClassTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            f.debug_struct("ClassTy")
                .field("name", &self.name)
                .field("parameters", &self.parameters)
                .finish()
        } else {
            match self.name {
                ClassName::Tuple(_) => {
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

use anyhow::bail;
use formality_core::parse::{CoreParse, Parser, Precedence};
use std::fmt::Debug;

use crate::dada_lang::FormalityLang;

use super::{NamedTy, Parameter, Perm, Ty, TypeName, ValueId};

impl NamedTy {
    /// Build an `Array[T]` named type from the parameters list, validating that
    /// there is exactly one type parameter. Returns both the `Array[T]` type and
    /// the element type `T`.
    pub fn array(parameters: &[Parameter]) -> anyhow::Result<(NamedTy, Ty)> {
        match parameters {
            [Parameter::Ty(element_ty)] => {
                let array_ty = NamedTy::new(TypeName::Array, parameters);
                Ok((array_ty, element_ty.clone()))
            }
            _ => bail!("Array requires exactly one type parameter, got {:?}", parameters),
        }
    }

    /// Extract parameters for `array_give[T, P, A]` and `array_drop[T, P, A]`.
    /// Returns (Array[T] named type, element type T, permission P, permission A).
    pub fn array_with_pa(parameters: &[Parameter]) -> anyhow::Result<(NamedTy, Ty, Perm, Perm)> {
        match parameters {
            [Parameter::Ty(element_ty), Parameter::Perm(perm_p), Parameter::Perm(perm_a)] => {
                let array_params: Vec<Parameter> = vec![Parameter::Ty(element_ty.clone())];
                let array_ty = NamedTy::new(TypeName::Array, array_params);
                Ok((array_ty, element_ty.clone(), perm_p.clone(), perm_a.clone()))
            }
            _ => bail!(
                "expected [T, P, A] (type, perm, perm) parameters, got {:?}",
                parameters
            ),
        }
    }

    /// Extract parameters for `array_write[T, A]` and `array_capacity[T, A]`.
    /// Returns (Array[T] named type, element type T, permission A).
    pub fn array_with_a(parameters: &[Parameter]) -> anyhow::Result<(NamedTy, Ty, Perm)> {
        match parameters {
            [Parameter::Ty(element_ty), Parameter::Perm(perm_a)] => {
                let array_params: Vec<Parameter> = vec![Parameter::Ty(element_ty.clone())];
                let array_ty = NamedTy::new(TypeName::Array, array_params);
                Ok((array_ty, element_ty.clone(), perm_a.clone()))
            }
            _ => bail!(
                "expected [T, A] (type, perm) parameters, got {:?}",
                parameters
            ),
        }
    }
}

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

            p.parse_variant("array", Precedence::default(), |p| {
                p.expect_keyword("Array")?;
                let parameters: Vec<Parameter> = p.delimited_nonterminal('[', false, ']')?;
                Ok(NamedTy::new(TypeName::Array, parameters))
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

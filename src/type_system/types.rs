use anyhow::bail;
use fn_error_context::context;
use formality_core::Fallible;

use crate::grammar::{NamedTy, Parameter, Perm, Place, Program, Ty, TypeName};

use super::{env::Env, places::place_ty};

pub fn check_parameter(env: &Env, parameter: &Parameter) -> Fallible<()> {
    match parameter {
        Parameter::Ty(ty) => check_type(env, ty),
        Parameter::Perm(perm) => check_perm(env, perm),
    }
}

#[context("check type `{:?}`", ty)]
pub fn check_type(env: &Env, ty: &Ty) -> Fallible<()> {
    match ty {
        Ty::NamedTy(NamedTy { name, parameters }) => {
            let arity = check_class_name(env.program(), name)?;
            if parameters.len() != arity {
                bail!(
                    "class `{:?}` expects {} parameters, but found {}",
                    name,
                    arity,
                    parameters.len(),
                )
            }

            for parameter in parameters {
                check_parameter(env, parameter)?;
            }
        }

        Ty::Var(v) => {
            assert!(env.var_in_scope(*v));
        }

        Ty::ApplyPerm(perm, ty1) => {
            check_perm(env, perm)?;
            check_type(env, ty1)?;
        }

        Ty::Or(l, r) => {
            check_type(env, l)?;
            check_type(env, r)?;
        }
    }
    Ok(())
}

#[context("check_perm({:?}", perm)]
fn check_perm(env: &Env, perm: &Perm) -> Fallible<()> {
    match perm {
        Perm::My | Perm::Our => {}

        Perm::Shared(places) => {
            for place in places {
                check_place(env, place)?;
            }
        }

        Perm::Given(places) | Perm::Leased(places) => {
            if places.len() == 0 {
                bail!("permision requires at lease one place");
            }

            for place in places {
                check_place(env, place)?;
            }
        }

        Perm::Var(v) => {
            assert!(env.var_in_scope(*v));
        }

        Perm::Apply(l, r) | Perm::Or(l, r) => {
            check_perm(env, l)?;
            check_perm(env, r)?;
        }
    }
    Ok(())
}

#[context("check class name `{:?}`", name)]
fn check_class_name(program: &Program, name: &TypeName) -> Fallible<usize> {
    match name {
        TypeName::Tuple(n) => Ok(*n),
        TypeName::Int => Ok(0),
        TypeName::Id(id) => {
            let decl = program.class_named(id)?;
            Ok(decl.binder.len())
        }
    }
}

#[context("check place `{:?}`", place)]
fn check_place(env: &Env, place: &Place) -> Fallible<()> {
    Ok(place_ty(env, place).check_proven()?)
}

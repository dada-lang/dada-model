use anyhow::bail;
use fn_error_context::context;
use formality_core::Fallible;

use crate::grammar::{NamedTy, Perm, Place, Program, Ty, TypeName};

use super::{env::Env, type_places::place_ty};

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
        }

        Ty::Var(v) => {
            assert!(env.var_in_scope(*v));
        }

        Ty::ApplyPerm(perm, ty1) => {
            check_perm(env, perm)?;
            check_type(env, ty1)?;
        }
    }
    Ok(())
}

#[context("check_perm({:?}", perm)]
fn check_perm(env: &Env, perm: &Perm) -> Fallible<()> {
    match perm {
        Perm::My => {}

        Perm::Shared(places) => {
            for place in places {
                check_place(env, place)?;
            }
        }

        Perm::Given(places) | Perm::Leased(places) | Perm::ShLeased(places) => {
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

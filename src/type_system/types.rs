use anyhow::bail;
use fn_error_context::context;
use formality_core::Fallible;

use crate::grammar::{ClassName, ClassTy, Perm, Place, Program, Ty};

use super::{env::Env, type_places::type_place};

#[context("check type `{:?}`", ty)]
pub fn check_type(env: &Env, ty: &Ty) -> Fallible<()> {
    match ty {
        Ty::ClassTy(ClassTy { name, parameters }) => {
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
        Perm::Owned => (),
        Perm::Shared(places, perm1) => {
            for place in places {
                check_place(env, place)?;
            }
            check_perm(env, perm1)?;
        }
        Perm::Leased(places, perm1) => {
            if places.len() == 0 {
                bail!("`leased` permision requires at lease one place to lease from");
            }
            for place in places {
                check_place(env, place)?;
            }
            check_perm(env, perm1)?;
        }
        Perm::Var(v, perm1) => {
            assert!(env.var_in_scope(*v));
            check_perm(env, perm1)?;
        }
    }
    Ok(())
}

#[context("check class name `{:?}`", name)]
fn check_class_name(program: &Program, name: &ClassName) -> Fallible<usize> {
    match name {
        ClassName::Tuple(n) => Ok(*n),
        ClassName::Int => Ok(0),
        ClassName::Id(id) => {
            let decl = program.class_named(id)?;
            Ok(decl.binder.len())
        }
    }
}

#[context("check place `{:?}`", place)]
fn check_place(env: &Env, place: &Place) -> Fallible<()> {
    if type_place(env, place).is_empty() {
        bail!("invalid place: `{place:?}`");
    } else {
        Ok(())
    }
}

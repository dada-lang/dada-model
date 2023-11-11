use anyhow::bail;
use fn_error_context::context;
use formality_core::Fallible;

use crate::grammar::{ClassName, ClassTy, Perm, Place, Program, Ty};

use super::{env::Env, type_places::type_place};

#[context("check type `{:?}`", ty)]
pub fn check_type(program: &Program, env: &Env, ty: &Ty) -> Fallible<()> {
    match ty {
        Ty::ClassTy(ClassTy {
            perm,
            name,
            parameters,
        }) => {
            check_perm(program, env, perm)?;

            let arity = check_class_name(program, name)?;
            if parameters.len() != arity {
                bail!(
                    "class `{:?}` expects {} parameters, but found {}",
                    name,
                    arity,
                    parameters.len(),
                )
            }
        }

        Ty::TupleTy(tys) => {
            for ty in tys {
                check_type(program, env, ty)?;
            }
        }

        Ty::Var(v) => {
            assert!(env.var_in_scope(*v));
        }
    }
    Ok(())
}

#[context("check_perm({:?}", perm)]
fn check_perm(program: &Program, env: &Env, perm: &Perm) -> Fallible<()> {
    match perm {
        Perm::My => (),
        Perm::Shared(places) => {
            for place in places {
                check_place(program, env, place)?;
            }
        }
        Perm::Leased(places) => {
            if places.len() == 0 {
                bail!("`leased` permision requires at lease one place to lease from");
            }
            for place in places {
                check_place(program, env, place)?;
            }
        }
        Perm::Var(v) => {
            assert!(env.var_in_scope(*v));
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
fn check_place(program: &Program, env: &Env, place: &Place) -> Fallible<()> {
    if type_place(program, env, place).is_empty() {
        bail!("invalid place: `{place:?}`");
    } else {
        Ok(())
    }
}

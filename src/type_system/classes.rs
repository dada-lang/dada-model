use std::sync::Arc;

use fn_error_context::context;
use formality_core::Fallible;

use crate::grammar::{Atomic, ClassDecl, ClassDeclBoundData, ClassTy, FieldDecl, Program};

use super::{env::Env, methods::check_method, types::check_type};

#[context("check class named `{:?}`", decl.name)]
pub fn check_class(program: &Arc<Program>, decl: &ClassDecl) -> Fallible<()> {
    let mut env = Env::new(program);

    let ClassDecl { name, binder } = decl;
    let (substitution, ClassDeclBoundData { fields, methods }) = env.open_universally(binder);

    let class_ty = ClassTy::new(name, &substitution);

    for field in fields {
        check_field(&class_ty, &env, &field)?;
    }

    for method in methods {
        check_method(&class_ty, &env, &method)?;
    }

    Ok(())
}

#[context("check field named `{:?}`", decl.name)]
fn check_field(_class_ty: &ClassTy, env: &Env, decl: &FieldDecl) -> Fallible<()> {
    let FieldDecl {
        atomic,
        name: _,
        ty,
    } = decl;
    check_type(env, ty)?;

    match atomic {
        Atomic::No => {}

        Atomic::Yes => {
            // FIXME: Check that any perm/type variables used in this field's type
            // are declared atomic.
        }
    }

    Ok(())
}

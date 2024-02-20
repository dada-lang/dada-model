use std::sync::Arc;

use fn_error_context::context;
use formality_core::Fallible;

use crate::grammar::{
    Atomic, ClassDecl, ClassDeclBoundData, FieldDecl, NamedTy, Program, Var, VarianceKind,
};

use super::{
    env::Env,
    methods::check_method,
    predicates::{check_predicate, prove_predicate},
    types::check_type,
};

#[context("check class named `{:?}`", decl.name)]
pub fn check_class(program: &Arc<Program>, decl: &ClassDecl) -> Fallible<()> {
    let mut env = Env::new(program);

    let ClassDecl { name, binder } = decl;
    let (
        substitution,
        ClassDeclBoundData {
            predicates,
            fields,
            methods,
        },
    ) = env.open_universally(binder);

    let class_ty = NamedTy::new(name, &substitution);

    env.add_assumptions(&predicates);

    for predicate in predicates {
        check_predicate(&env, &predicate)?;
    }

    for field in fields {
        check_field(&class_ty, &env, &field)?;
    }

    for method in methods {
        check_method(&class_ty, &env, &method)?;
    }

    Ok(())
}

#[context("check field named `{:?}`", decl.name)]
fn check_field(class_ty: &NamedTy, env: &Env, decl: &FieldDecl) -> Fallible<()> {
    let env = &mut env.clone();

    let FieldDecl {
        atomic,
        name: _,
        ty,
    } = decl;

    env.push_local_variable(Var::This, class_ty)?;

    check_type(&*env, ty)?;

    match atomic {
        Atomic::No => {}

        Atomic::Yes => {
            prove_predicate(&*env, VarianceKind::Atomic.apply(ty)).check_proven()?;
        }
    }

    Ok(())
}

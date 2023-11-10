use fn_error_context::context;
use formality_core::Fallible;

use crate::grammar::{ClassDecl, ClassDeclBoundData, FieldDecl, Program};

use super::env::Env;

#[context("check_class({:?}", decl.name)]
pub fn check_class(program: &Program, decl: &ClassDecl) -> Fallible<()> {
    let mut env = Env::default();

    let ClassDeclBoundData { fields } = env.open_universally(&decl.binder);

    for field in fields {
        check_field(program, &env, &field);
    }

    Ok(())
}

#[context("check_field({:?}", decl)]
fn check_field(program: &Program, env: &Env, decl: &FieldDecl) -> Fallible<()> {
    Ok(())
}

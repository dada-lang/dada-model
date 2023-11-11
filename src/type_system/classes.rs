use fn_error_context::context;
use formality_core::Fallible;

use crate::grammar::{ClassDecl, ClassDeclBoundData, FieldDecl, Program};

use super::{env::Env, types::check_type};

#[context("check class named `{:?}`", decl.name)]
pub fn check_class(program: &Program, decl: &ClassDecl) -> Fallible<()> {
    let mut env = Env::default();

    let ClassDeclBoundData { fields } = env.open_universally(&decl.binder);

    for field in fields {
        check_field(program, &env, &field)?;
    }

    Ok(())
}

#[context("check field named `{:?}`", decl.name)]
fn check_field(program: &Program, env: &Env, decl: &FieldDecl) -> Fallible<()> {
    let FieldDecl { name: _, ty } = decl;
    check_type(program, env, ty)?;
    Ok(())
}

use fn_error_context::context;
use formality_core::Fallible;

use crate::grammar::{FnDecl, FnDeclBoundData, Program};

use super::env::Env;

#[context("check_fn({:?}", decl.name)]
pub fn check_fn(program: &Program, decl: &FnDecl) -> Fallible<()> {
    let mut env = Env::default();

    let FnDeclBoundData {
        inputs,
        output,
        body,
    } = env.open_universally(&decl.binder);

    Ok(())
}

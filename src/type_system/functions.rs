use anyhow::bail;
use fn_error_context::context;
use formality_core::Fallible;

use crate::grammar::{Block, FnDecl, FnDeclBoundData, LocalVariableDecl, Program, Ty};

use super::{env::Env, type_expr::can_type_expr_as, types::check_type};

#[context("check function named `{:?}`", decl.name)]
pub fn check_fn(program: &Program, decl: &FnDecl) -> Fallible<()> {
    let env = &mut Env::default();

    let FnDeclBoundData {
        inputs,
        output,
        body,
    } = &env.open_universally(&decl.binder);

    inputs
        .iter()
        .for_each(|input| env.push_local_variable_decl(input));

    for input in inputs {
        let LocalVariableDecl { name: _, ty } = input;
        check_type(program, env, ty)?;
    }

    check_type(program, env, output)?;

    check_body(program, env, output, body)?;

    Ok(())
}

#[context("check function body")]
fn check_body(program: &Program, env: &Env, output: &Ty, body: &Block) -> Fallible<()> {
    if can_type_expr_as(program, env, body, output).is_empty() {
        bail!("type check for fn body failed");
    }

    Ok(())
}

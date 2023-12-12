use std::sync::Arc;

use anyhow::bail;
use fn_error_context::context;
use formality_core::{Fallible, Upcast};

use crate::grammar::{Block, FnDecl, FnDeclBoundData, LocalVariableDecl, Program, Ty};

use super::{env::Env, flow::Flow, type_expr::can_type_expr_as, types::check_type};

#[context("check function named `{:?}`", decl.name)]
pub fn check_fn(program: impl Upcast<Arc<Program>>, decl: &FnDecl) -> Fallible<()> {
    let program: Arc<Program> = program.upcast();
    let env = &mut Env::new(&program);

    let FnDeclBoundData {
        inputs,
        output,
        body,
    } = &env.open_universally(&decl.binder);

    for input in inputs {
        env.push_local_variable_decl(input)?;
    }

    for input in inputs {
        let LocalVariableDecl { name: _, ty } = input;
        check_type(env, ty)?;
    }

    check_type(env, output)?;

    check_body(env, output, body)?;

    Ok(())
}

#[context("check function body")]
fn check_body(env: &Env, output: &Ty, body: &Block) -> Fallible<()> {
    let flow = Flow::default();
    if can_type_expr_as(env, flow, body, output).is_empty() {
        bail!("type check for fn body failed");
    }

    Ok(())
}

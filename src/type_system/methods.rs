use fn_error_context::context;
use formality_core::{Fallible, Upcast};

use crate::grammar::{
    Block, LocalVariableDecl, MethodDecl, MethodDeclBoundData, NamedTy, ThisDecl, Ty, Var::This,
};

use super::{env::Env, flow::Flow, type_expr::can_type_expr_as, types::check_type};

#[context("check method named `{:?}`", decl.name)]
pub fn check_method(class_ty: &NamedTy, env: impl Upcast<Env>, decl: &MethodDecl) -> Fallible<()> {
    let mut env = env.upcast();

    let MethodDecl { name: _, binder } = decl;
    let (
        _,
        MethodDeclBoundData {
            this,
            inputs,
            output,
            body,
        },
    ) = &env.open_universally(binder);

    if let Some(ThisDecl { perm }) = this {
        let this_ty = Ty::apply_perm(perm, class_ty);
        env.push_local_variable_decl(LocalVariableDecl {
            name: This,
            ty: this_ty,
        })?;
    }

    for input in inputs {
        env.push_local_variable_decl(input)?;
    }

    for input in inputs {
        let LocalVariableDecl { name: _, ty } = input;
        check_type(&env, ty)?;
    }

    check_type(&env, output)?;

    check_body(&env, output, body)?;

    Ok(())
}

#[context("check function body")]
fn check_body(env: &Env, output: &Ty, body: &Block) -> Fallible<()> {
    let flow = Flow::default();
    Ok(can_type_expr_as(env, flow, body, output).check_proven()?)
}

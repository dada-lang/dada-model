use fn_error_context::context;
use formality_core::{Fallible, Upcast};

use crate::grammar::{
    LocalVariableDecl, MethodBody, MethodDecl, MethodDeclBoundData, NamedTy, ThisDecl, Ty,
    Var::This, VarianceKind,
};

use super::{
    env::Env, expressions::can_type_expr_as, liveness::LivePlaces, predicates::check_predicates,
    types::check_type,
};

#[context("check method named `{:?}`", decl.name)]
pub fn check_method(class_ty: &NamedTy, env: impl Upcast<Env>, decl: &MethodDecl) -> Fallible<()> {
    let mut env = env.upcast();

    let MethodDecl { name: _, binder } = decl;
    let (
        vars,
        MethodDeclBoundData {
            this,
            inputs,
            output,
            predicates,
            body,
        },
    ) = &env.open_universally(binder);

    // Methods don't really care about variance, so they can assume all their
    // parameters are relative/atomic for purposes of WF checking.
    env.add_assumptions(
        vars.iter()
            .flat_map(|v| {
                vec![
                    VarianceKind::Relative.apply(&v),
                    VarianceKind::Atomic.apply(&v),
                ]
            })
            .collect::<Vec<_>>(),
    );

    check_predicates(&env, predicates)?;

    env.add_assumptions(predicates);

    let ThisDecl { perm: this_perm } = this;
    let this_ty = Ty::apply_perm(this_perm, class_ty);
    env.push_local_variable(This, this_ty)?;

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
fn check_body(env: &Env, output: &Ty, body: &MethodBody) -> Fallible<()> {
    let live_after = LivePlaces::default();
    match body {
        MethodBody::Trusted => Ok(()),
        MethodBody::Block(block) => {
            Ok(can_type_expr_as(env, live_after, block, output).check_proven()?)
        }
    }
}

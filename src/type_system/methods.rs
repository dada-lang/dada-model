use fn_error_context::context;
use formality_core::{judgment::ProofTree, Fallible, Upcast};

use crate::grammar::{
    LocalVariableDecl, MethodBody, MethodDecl, MethodDeclBoundData, NamedTy, ThisDecl, Ty,
    Var::This, VarianceKind,
};

use super::{
    env::Env, expressions::can_type_expr_as, liveness::LivePlaces, predicates::check_predicates,
    types::check_type,
};

// ANCHOR: check_method
#[context("check method named `{:?}`", decl.name)]
pub fn check_method(
    class_ty: &NamedTy,
    env: impl Upcast<Env>,
    decl: &MethodDecl,
) -> Fallible<ProofTree> {
    let mut env = env.upcast();
    let mut proof_tree = ProofTree::new(format!("check_method({:?})", decl.name), None, vec![]);

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

    proof_tree
        .children
        .push(check_predicates(&env, predicates)?);

    env.add_assumptions(predicates);

    let ThisDecl { perm: this_perm } = this;
    let this_ty = Ty::apply_perm(this_perm, class_ty);
    env.push_local_variable(This, this_ty)?;

    for input in inputs {
        env.push_local_variable_decl(input)?;
    }

    for input in inputs {
        let LocalVariableDecl { name: _, ty } = input;
        proof_tree.children.push(check_type(&env, ty)?);
    }

    proof_tree.children.push(check_type(&env, output)?);

    proof_tree.children.push(check_body(&env, output, body)?);

    Ok(proof_tree)
}
// ANCHOR_END: check_method

// ANCHOR: check_body
#[context("check function body")]
fn check_body(env: &Env, output: &Ty, body: &MethodBody) -> Fallible<ProofTree> {
    let live_after = LivePlaces::default();
    match body {
        MethodBody::Trusted => Ok(ProofTree::leaf("check_body(trusted)")),
        MethodBody::Block(block) => {
            let ((), child) =
                can_type_expr_as(env, live_after, block, output).into_singleton()?;
            Ok(child)
        }
    }
}
// ANCHOR_END: check_body

use formality_core::{judgment_fn, Cons, ProvenSet};

use crate::{
    grammar::{Access, Ascription, Statement, Ty},
    type_system::{
        accesses::env_permits_access,
        env::Env,
        expressions::{type_expr, type_expr_as},
        flow::Flow,
        places::place_ty,
    },
};

use super::liveness::LiveVars;

pub fn type_statements(
    env: Env,
    flow: Flow,
    live_after: LiveVars,
    statements: Vec<Statement>,
) -> ProvenSet<(Env, Flow, Ty)> {
    type_statements_with_final_ty(env, flow, live_after, statements, Ty::unit())
}

judgment_fn! {
    fn type_statements_with_final_ty(
        env: Env,
        flow: Flow,
        live_after: LiveVars,
        statements: Vec<Statement>,
        ty: Ty,
    ) => (Env, Flow, Ty) {
        debug(statements, ty, env, flow, live_after)

        (
            ----------------------------------- ("nil")
            (type_statements_with_final_ty(env, flow, _live_after, (), ty) => (env, flow, ty))
        )

        (
            (let live = live_after.before(&statements))
            (type_statement(env, flow, live, &statement) => (env, flow, ty))
            (type_statements_with_final_ty(env, flow, &live_after, &statements, ty) => (env, flow, ty))
            ----------------------------------- ("cons")
            (type_statements_with_final_ty(env, flow, live_after, Cons(statement, statements), _ty) => (env, flow, ty))
        )
    }
}

judgment_fn! {
    fn type_statement(
        env: Env,
        flow: Flow,
        live_after: LiveVars,
        statement: Statement,
    ) => (Env, Flow, Ty) {
        debug(statement, env, flow, live_after)

        (
            (type_expr(env, flow, live_after, expr) => (env, flow, ty))
            ----------------------------------- ("expr")
            (type_statement(env, flow, live_after, Statement::Expr(expr)) => (env, flow, ty))
        )

        (
            (type_expr(env, flow, live_after.without(&id), &*expr) => (env, flow, ty)) // [1]
            (env.with(|e| e.push_local_variable(&id, ty)) => (env, ()))
            ----------------------------------- ("let")
            (type_statement(env, flow, live_after, Statement::Let(id, Ascription::NoTy, expr)) => (env, &flow, Ty::unit()))
        )

        (
            (type_expr_as(env, flow, live_after.without(&id), &*expr, &ty) => (env, flow)) // [1]
            (env.with(|e| e.push_local_variable(&id, &ty)) => (env, ()))
            ----------------------------------- ("let")
            (type_statement(env, flow, live_after, Statement::Let(id, Ascription::Ty(ty), expr)) => (env, &flow, Ty::unit()))
        )

        // [1] Subtle: The set of variables live after `let x = <expr>` may include `x`,
        // but the set of variables live after `<expr>` does not.

        (
            // FIXME: should be live_after.without(place) -- or at least if place is just a variable
            (place_ty(&env, &place) => ty)
            (type_expr_as(&env, &flow, &live_after, &expr, ty) => (env, flow))
            (env_permits_access(env, flow, &live_after, Access::Lease, &place) => (env, flow))
            (let flow = flow.assign_place(&place))
            ----------------------------------- ("let")
            (type_statement(env, flow, live_after, Statement::Reassign(place, expr)) => (env, &flow, Ty::unit()))
        )
    }
}

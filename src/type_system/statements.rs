use formality_core::{judgment_fn, Cons, ProvenSet};

use crate::{
    grammar::{Access, Statement, Ty},
    type_system::{
        accesses::env_permits_access,
        env::Env,
        expressions::{type_expr, type_expr_as},
        flow::Flow,
        liveness::adjust_for_liveness,
        places::place_ty,
    },
};

pub fn type_statements(
    env: Env,
    flow: Flow,
    statements: Vec<Statement>,
) -> ProvenSet<(Env, Flow, Ty)> {
    type_statements_with_final_ty(env, flow, statements, Ty::unit())
}

judgment_fn! {
    fn type_statements_with_final_ty(
        env: Env,
        flow: Flow,
        statements: Vec<Statement>,
        ty: Ty,
    ) => (Env, Flow, Ty) {
        debug(statements, ty, env, flow)

        (
            ----------------------------------- ("nil")
            (type_statements_with_final_ty(env, flow, (), ty) => (env, flow, ty))
        )

        (
            (adjust_for_liveness(env, flow) => (env, flow))
            (type_statement(env, flow, &statement) => (env, flow, ty))
            (type_statements_with_final_ty(env, flow, &statements, ty) => (env, flow, ty))
            ----------------------------------- ("cons")
            (type_statements_with_final_ty(env, flow, Cons(statement, statements), _ty) => (env, flow, ty))
        )
    }
}

judgment_fn! {
    fn type_statement(
        env: Env,
        flow: Flow,
        statement: Statement,
    ) => (Env, Flow, Ty) {
        debug(statement, env, flow)

        (
            (type_expr(env, flow, expr) => (env, flow, ty))
            ----------------------------------- ("expr")
            (type_statement(env, flow, Statement::Expr(expr)) => (env, flow, ty))
        )

        (
            (type_expr(env, flow, &*expr) => (env, flow, ty))
            (env.with(|e| e.push_local_variable(&id, ty)) => (env, ()))
            ----------------------------------- ("let")
            (type_statement(env, flow, Statement::Let(id, expr)) => (env, &flow, Ty::unit()))
        )

        (
            (place_ty(&env, &place) => ty)
            (type_expr_as(&env, &flow, &expr, ty) => (env, flow))
            (env_permits_access(env, flow, Access::Lease, &place) => (env, flow))
            (let flow = flow.assign_place(&place))
            ----------------------------------- ("let")
            (type_statement(env, flow, Statement::Reassign(place, expr)) => (env, &flow, Ty::unit()))
        )
    }
}

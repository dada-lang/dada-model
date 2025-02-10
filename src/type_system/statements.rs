use formality_core::{judgment_fn, Cons, ProvenSet};

use crate::{
    grammar::{Access, Ascription, Statement, Ty},
    type_system::{
        accesses::{env_permits_access, parameter_permits_access},
        env::Env,
        expressions::{type_expr, type_expr_as},
        in_flight::InFlight,
        predicates::prove_is_move_if_some,
    },
};

use super::liveness::LivePlaces;

pub fn type_statements(
    env: Env,
    live_after: LivePlaces,
    statements: Vec<Statement>,
) -> ProvenSet<(Env, Ty)> {
    type_statements_with_final_ty(env, live_after, statements, Ty::unit())
}

judgment_fn! {
    fn type_statements_with_final_ty(
        env: Env,
        live_after: LivePlaces,
        statements: Vec<Statement>,
        ty: Ty,
    ) => (Env, Ty) {
        debug(statements, ty, env, live_after)

        (
            ----------------------------------- ("nil")
            (type_statements_with_final_ty(env, _live_after, (), ty) => (env, ty))
        )

        (
            (let live = live_after.before(&statements))
            (type_statement(env, live, &statement) => (env, ty))
            (type_statements_with_final_ty(env, &live_after, &statements, ty) => (env, ty))
            ----------------------------------- ("cons")
            (type_statements_with_final_ty(env, live_after, Cons(statement, statements), _ty) => (env, ty))
        )
    }
}

judgment_fn! {
    fn type_statement(
        env: Env,
        live_after: LivePlaces,
        statement: Statement,
    ) => (Env, Ty) {
        debug(statement, env, live_after)

        (
            (type_expr(env, &live_after, expr) => (env, ty))
            (let (env, temp) = env.push_fresh_variable_with_in_flight(&ty))
            (env_permits_access(env, &live_after, Access::Drop, &temp) => env)
            (parameter_permits_access(env, &ty, Access::Drop, &temp) => env)
            (let env = env.pop_fresh_variable(&temp))
            ----------------------------------- ("expr")
            (type_statement(env, live_after, Statement::Expr(expr)) => (env, &ty))
        )

        (
            (type_expr(env, live_after.overwritten(&id), &*expr) => (env, ty)) // [1]
            (let (env, ()) = env.with(|e| e.push_local_variable(&id, ty))?)
            (let env = env.with_in_flight_stored_to(&id))
            ----------------------------------- ("let")
            (type_statement(env, live_after, Statement::Let(id, Ascription::NoTy, expr)) => (env, Ty::unit()))
        )

        (
            (type_expr_as(env, live_after.overwritten(&id), &*expr, &ty) => env) // [1]
            (let (env, ()) = env.with(|e| e.push_local_variable(&id, &ty))?)
            (let env = env.with_in_flight_stored_to(&id))
            ----------------------------------- ("let")
            (type_statement(env, live_after, Statement::Let(id, Ascription::Ty(ty), expr)) => (env, Ty::unit()))
        )

        // [1] Subtle: The set of variables live after `let x = <expr>` may include `x`,
        // but the set of variables live after `<expr>` does not.

        (
            (let (owner_ty, field_ty) = env.owner_and_field_ty(&place)?)
            (type_expr_as(&env, live_after.clone().overwritten(&place), &expr, &field_ty) => env)
            (let (env, temp) = env.push_fresh_variable_with_in_flight(&field_ty))
            (prove_is_move_if_some(&env, &owner_ty) => ())
            (env_permits_access(&env, &live_after, Access::Lease, &place) => env)
            (let env = env.with_var_stored_to(&temp, &place))
            (let env = env.pop_fresh_variable(&temp))
            ----------------------------------- ("reassign")
            (type_statement(env, live_after, Statement::Reassign(place, expr)) => (env, Ty::unit()))
        )
    }
}

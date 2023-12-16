use formality_core::{judgment_fn, Cons};

use crate::{
    grammar::{Block, ClassName, Expr, Statement, Ty},
    type_system::{
        env::Env, flow::Flow, quantifiers::fold, type_places::type_place, type_subtype::sub,
    },
};

judgment_fn! {
    pub fn can_type_expr_as(
        env: Env,
        flow: Flow,
        expr: Expr,
        as_ty: Ty,
    ) => () {
        debug(expr, as_ty, env, flow)

        (
            (type_expr_as(env, flow, expr, as_ty) => _)
            -------------------------------- ("can_type_expr_as")
            (can_type_expr_as(env, flow, expr, as_ty) => ())
        )
    }
}

judgment_fn! {
    pub fn type_expr_as(
        env: Env,
        flow: Flow,
        expr: Expr,
        as_ty: Ty,
    ) => (Env, Flow) {
        debug(expr, as_ty, env, flow)

        (
            (type_expr(env, flow, expr) => (env, flow, ty))
            (sub(env, flow, ty, &as_ty) => (env, flow))
            -------------------------------- ("can_type_expr_as")
            (type_expr_as(env, flow, expr, as_ty) => (env, flow))
        )
    }
}

judgment_fn! {
    pub fn type_expr(
        env: Env,
        flow: Flow,
        expr: Expr,
    ) => (Env, Flow, Ty) {
        debug(expr, env, flow)

        (
            (type_block(env, flow, block) => (env, flow, ty))
            ----------------------------------- ("block")
            (type_expr(env, flow, Expr::Block(block)) => (env, flow, ty))
        )

        (
            ----------------------------------- ("block")
            (type_expr(env, flow, Expr::Integer(_)) => (env, flow, Ty::int()))
        )

        (
            (type_exprs(env, flow, exprs) => (env, flow, tys))
            ----------------------------------- ("tuple")
            (type_expr(env, flow, Expr::Tuple(exprs)) => (env, flow, Ty::tuple(tys)))
        )

        (
            (type_place(&env, value_id) => _ty)
            // FIXME: This should remove `value_id` from the environment.
            ----------------------------------- ("clear")
            (type_expr(env, flow, Expr::Clear(value_id)) => (&env, &flow, Ty::unit()))
        )

        (
            (type_expr_as(&env, flow, &*cond, ClassName::Int) => (env, flow_cond))
            (type_expr(&env, &flow_cond, &*if_true) => (env, flow_if_true, if_true_ty))
            (type_expr(&env, &flow_cond, &*if_false) => (env, flow_if_false, if_false_ty))
            (let flow = flow_if_true.merge(&flow_if_false))
            (env.with(|env| Ok(env.mutual_supertype(&if_true_ty, &if_false_ty))) => (env, ty))
            ----------------------------------- ("if")
            (type_expr(env, flow, Expr::If(cond, if_true, if_false)) => (&env, &flow, ty))
        )
    }
}

judgment_fn! {
    pub fn type_exprs(
        env: Env,
        flow: Flow,
        exprs: Vec<Expr>,
    ) => (Env, Flow, Vec<Ty>) {
        debug(exprs, env, flow)

        (
            ----------------------------------- ("none")
            (type_exprs(env, flow, ()) => (env, flow, ()))
        )

        (
            (type_expr(&env, flow, head) => (env, flow, head_ty))
            (type_exprs(&env, &flow, &tails) => (env, flow, tail_tys))
            ----------------------------------- ("one-or-more")
            (type_exprs(env, flow, Cons(head, tails)) => (env, flow, Cons(&head_ty, tail_tys)))
        )

    }
}

judgment_fn! {
    pub fn type_statement(
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
    }
}

judgment_fn! {
    pub fn type_block(
        env: Env,
        flow: Flow,
        block: Block,
    ) => (Env, Flow, Ty) {
        debug(block, env, flow)

        (
            (fold((env, flow, Ty::unit()), &statements, &|(env, flow, _), statement| type_statement(&env, flow, statement)) => (env, flow, ty))
            ----------------------------------- ("place")
            (type_block(env, flow, Block { statements }) => (env, flow, ty))
        )
    }
}

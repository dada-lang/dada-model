use formality_core::{judgment_fn, Cons};

use crate::{
    grammar::{Block, ClassName, Expr, Statement, Ty},
    type_system::{env::Env, quantifiers::fold, type_places::type_place, type_subtype::sub},
};

judgment_fn! {
    pub fn can_type_expr_as(
        env: Env,
        expr: Expr,
        as_ty: Ty,
    ) => () {
        debug(expr, as_ty, env)

        (
            (type_expr_as(env, expr, as_ty) => _)
            -------------------------------- ("can_type_expr_as")
            (can_type_expr_as(env, expr, as_ty) => ())
        )
    }
}

judgment_fn! {
    pub fn type_expr_as(
        env: Env,
        expr: Expr,
        as_ty: Ty,
    ) => Env {
        debug(expr, env, as_ty)

        (
            (type_expr(env, expr) => (env, ty))
            (sub(env, ty, &as_ty) => env)
            -------------------------------- ("can_type_expr_as")
            (type_expr_as(env, expr, as_ty) => env)
        )
    }
}

judgment_fn! {
    pub fn type_expr(
        env: Env,
        expr: Expr,
    ) => (Env, Ty) {
        debug(expr, env)

        (
            (type_block(env, block) => (env, ty))
            ----------------------------------- ("block")
            (type_expr(env, Expr::Block(block)) => (env, ty))
        )

        (
            ----------------------------------- ("block")
            (type_expr(env, Expr::Integer(_)) => (env, Ty::int()))
        )

        (
            (type_exprs(env, exprs) => (env, tys))
            ----------------------------------- ("tuple")
            (type_expr(env, Expr::Tuple(exprs)) => (env, Ty::tuple(tys)))
        )

        (
            (type_place(&env, value_id) => _ty)
            ----------------------------------- ("clear")
            (type_expr(env, Expr::Clear(value_id)) => (&env, Ty::unit()))
        )

        (
            (type_expr_as(&env, &*cond, ClassName::Int) => env0)
            (type_expr(&env0, &*if_true) => (if_true_env, if_true_ty))
            (type_expr(&env0, &*if_false) => (if_false_env, if_false_ty))
            ----------------------------------- ("if")
            (type_expr(env, Expr::If(cond, if_true, if_false)) => (&env, Ty::unit()))
        )
    }
}

judgment_fn! {
    pub fn type_exprs(
        env: Env,
        exprs: Vec<Expr>,
    ) => (Env, Vec<Ty>) {
        debug(exprs, env)

        (
            ----------------------------------- ("none")
            (type_exprs(_env, ()) => (env, ()))
        )

        (
            (type_expr(&env, head) => (env, head_ty))
            (type_exprs(&env, &tails) => (env, tail_tys))
            ----------------------------------- ("one-or-more")
            (type_exprs(env, Cons(head, tails)) => (env, Cons(&head_ty, tail_tys)))
        )

    }
}

judgment_fn! {
    pub fn type_statement(
        env: Env,
        statement: Statement,
    ) => (Env, Ty) {
        debug(statement, env)

        (
            (type_expr(env, expr) => (env, ty))
            ----------------------------------- ("expr")
            (type_statement(env, Statement::Expr(expr)) => (env, ty))
        )

        (
            (type_expr(env, &*expr) => (env, ty))
            (env.with(|e| e.push_local_variable(&id, ty)) => env)
            ----------------------------------- ("let")
            (type_statement(env, Statement::Let(id, expr)) => (env, Ty::unit()))
        )
    }
}

judgment_fn! {
    pub fn type_block(
        env: Env,
        block: Block,
    ) => (Env, Ty) {
        debug(block, env)

        (
            (fold((env, Ty::unit()), &statements, &|(env, _), statement| type_statement(&env, statement)) => (env, ty))
            ----------------------------------- ("place")
            (type_block(env, Block { statements }) => (env, ty))
        )
    }
}

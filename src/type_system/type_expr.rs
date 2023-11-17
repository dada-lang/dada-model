use formality_core::{judgment_fn, Cons};

use crate::{
    grammar::{Block, Expr, Program, Statement, Ty},
    type_system::{env::Env, quantifiers::fold, type_subtype::sub},
};

judgment_fn! {
    pub fn can_type_expr_as(
        program: Program,
        env: Env,
        expr: Expr,
        as_ty: Ty,
    ) => () {
        debug(expr, as_ty, program, env)

        (
            (type_expr_as(program, env, expr, as_ty) => _)
            -------------------------------- ("can_type_expr_as")
            (can_type_expr_as(program, env, expr, as_ty) => ())
        )
    }
}

judgment_fn! {
    pub fn type_expr_as(
        program: Program,
        env: Env,
        expr: Expr,
        as_ty: Ty,
    ) => Env {
        debug(expr, program, env, as_ty)

        (
            (type_expr(&program, env, expr) => (env, ty))
            (sub(&program, env, ty, &as_ty) => env)
            -------------------------------- ("can_type_expr_as")
            (type_expr_as(program, env, expr, as_ty) => env)
        )
    }
}

judgment_fn! {
    pub fn type_expr(
        program: Program,
        env: Env,
        expr: Expr,
    ) => (Env, Ty) {
        debug(expr, program, env)

        (
            (type_block(program, env, block) => (env, ty))
            ----------------------------------- ("block")
            (type_expr(program, env, Expr::Block(block)) => (env, ty))
        )

        (
            ----------------------------------- ("block")
            (type_expr(_program, env, Expr::Integer(_)) => (env, Ty::int()))
        )

        (
            (type_exprs(program, env, exprs) => (env, tys))
            ----------------------------------- ("tuple")
            (type_expr(program, env, Expr::Tuple(exprs)) => (env, Ty::tuple(tys)))
        )

        (
            ----------------------------------- ("clear")
            (type_expr(program, env, Expr::Clear(_place)) => (env, Ty::unit()))
        )
    }
}

judgment_fn! {
    pub fn type_exprs(
        program: Program,
        env: Env,
        exprs: Vec<Expr>,
    ) => (Env, Vec<Ty>) {
        debug(exprs, program, env)

        (
            ----------------------------------- ("none")
            (type_exprs(_program, env, ()) => (env, ()))
        )

        (
            (type_expr(&program, env, head) => (env, head_ty))
            (type_exprs(&program, env, &tails) => (env, tail_tys))
            ----------------------------------- ("one-or-more")
            (type_exprs(program, env, Cons(head, tails)) => (env, Cons(&head_ty, tail_tys)))
        )

    }
}

judgment_fn! {
    pub fn type_statement(
        program: Program,
        env: Env,
        statement: Statement,
    ) => (Env, Ty) {
        debug(statement, program, env)

        (
            (type_expr(program, env, expr) => (env, ty))
            ----------------------------------- ("expr")
            (type_statement(program, env, Statement::Expr(expr)) => (env, ty))
        )

        (
            (type_expr(program, env, &*expr) => (env, ty))
            (let env = env.with_var_ty(&id, ty))
            ----------------------------------- ("let")
            (type_statement(program, env, Statement::Let(id, expr)) => (env, Ty::unit()))
        )
    }
}

judgment_fn! {
    pub fn type_block(
        program: Program,
        env: Env,
        block: Block,
    ) => (Env, Ty) {
        debug(block, program, env)

        (
            (fold((env, Ty::unit()), &statements, &|(env, _), statement| type_statement(&program, env, statement)) => (env, ty))
            ----------------------------------- ("place")
            (type_block(program, env, Block { statements }) => (env, ty))
        )
    }
}

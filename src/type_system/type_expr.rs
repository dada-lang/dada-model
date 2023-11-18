use formality_core::{judgment_fn, Cons};

use crate::{
    grammar::{Block, ClassName, Expr, Program, Statement, Ty},
    type_system::{env::Env, quantifiers::fold, type_places::type_place, type_subtype::sub},
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
            (type_place(program, &env, value_id) => _ty)
            ----------------------------------- ("clear")
            (type_expr(program, env, Expr::Clear(value_id)) => (&env, Ty::unit()))
        )

        (
            (type_expr_as(&program, &env, &*cond, ClassName::Int) => env0)
            (type_expr(&program, &env0, &*if_true) => (if_true_env, if_true_ty))
            (type_expr(&program, &env0, &*if_false) => (if_false_env, if_false_ty))
            ----------------------------------- ("if")
            (type_expr(program, env, Expr::If(cond, if_true, if_false)) => (&env, Ty::unit()))
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

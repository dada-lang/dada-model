use formality_core::judgment_fn;

use crate::{
    grammar::{
        Block, ClassDeclBoundData, ClassName, ClassTy, Expr, FieldId, Place, Program, Projection,
        Statement, Ty,
    },
    type_system::{env::Env, quantifiers::fold},
};

judgment_fn! {
    pub fn type_expr(
        program: Program,
        env: Env,
        expr: Expr,
    ) => (Env, Ty) {
        debug(expr, program, env)
    }
}

judgment_fn! {
    pub fn type_statement(
        program: Program,
        env: Env,
        statement: Statement,
    ) => Env {
        debug(statement, program, env)

        (
            (type_expr(program, env, expr) => (env, _ty))
            ----------------------------------- ("expr")
            (type_statement(program, env, Statement::Expr(expr)) => env)
        )

        (
            (type_expr(program, env, &*expr) => (env, ty))
            (let env = env.with_variable(id, ty))
            ----------------------------------- ("let")
            (type_statement(program, env, Statement::Let(id, expr)) => env)
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
            (fold(env, &statements, &|env, statement| type_statement(program, env, statement)) => env)
            (type_expr(program, env, &*tail_expr) => (env, ty))
            ----------------------------------- ("place")
            (type_block(program, env, Block { statements, tail_expr }) => (env, ty))
        )
    }
}

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

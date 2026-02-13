use formality_core::judgment_fn;

use crate::grammar::{
    LocalVariableDecl, MethodBody, MethodDecl, MethodDeclBoundData, NamedTy, ThisDecl, Ty,
    Var::This, VarianceKind,
};

use super::{
    env::Env, expressions::can_type_expr_as, liveness::LivePlaces, predicates::check_predicates,
    quantifiers::for_all, types::check_type,
};

// ANCHOR: check_method
judgment_fn! {
    pub fn check_method(
        class_ty: NamedTy,
        env: Env,
        decl: MethodDecl,
    ) => () {
        debug(decl, class_ty, env)

        (
            (let MethodDecl { name: _, binder } = decl)
            (let (env, vars, MethodDeclBoundData { this, inputs, output, predicates, body }) =
                env.open_universally(&binder))

            // Methods don't really care about variance, so they can assume all their
            // parameters are relative/atomic for purposes of WF checking.
            (let env = env.add_assumptions(
                vars.iter()
                    .flat_map(|v| vec![VarianceKind::Relative.apply(v), VarianceKind::Atomic.apply(v)])
                    .collect::<Vec<_>>(),
            ))

            (check_predicates(&env, &predicates) => ())
            (let env = env.add_assumptions(&predicates))

            (let ThisDecl { perm: this_perm } = &this)
            (let this_ty = Ty::apply_perm(this_perm, &class_ty))
            (let env = env.push_local_variable(This, &this_ty)?)

            (let env = env.push_local_variable_decls(&inputs)?)

            (for_all(inputs, &|input| { let LocalVariableDecl { name: _, ty } = input; check_type(&env, ty) }) => ())

            (check_type(&env, &output) => ())

            (check_body(&env, &output, &body) => ())
            ----------------------------------- ("check_method")
            (check_method(class_ty, env, decl) => ())
        )
    }
}
// ANCHOR_END: check_method

// ANCHOR: check_body
judgment_fn! {
    fn check_body(
        env: Env,
        output: Ty,
        body: MethodBody,
    ) => () {
        debug(body, output, env)

        (
            ----------------------------------- ("trusted")
            (check_body(_env, _output, MethodBody::Trusted) => ())
        )

        (
            (let live_after = LivePlaces::default())
            (can_type_expr_as(env, live_after, block, output) => ())
            ----------------------------------- ("block")
            (check_body(env, output, MethodBody::Block(block)) => ())
        )
    }
}
// ANCHOR_END: check_body

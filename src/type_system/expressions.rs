use formality_core::{judgment_fn, set, Cons};

use crate::{
    grammar::{Access, ClassDeclBoundData, Expr, NamedTy, Perm, Place, PlaceExpr, Ty, TypeName},
    type_system::{
        accesses::access_permitted, blocks::type_block, env::Env, flow::Flow, places::place_ty,
        subtypes::sub,
    },
};

use super::subtypes::is_shared;

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
            -------------------------------- ("type_expr_as")
            (type_expr_as(env, flow, expr, as_ty) => (env, flow))
        )
    }
}

judgment_fn! {
    /// Compute the type of an expression in the given environment.
    /// Requires that the expression is valid in that environment --
    /// i.e., does not access moved state.
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
            ----------------------------------- ("constant")
            (type_expr(env, flow, Expr::Integer(_)) => (env, flow, Ty::int()))
        )

        (
            (type_expr_as(env, flow, &*lhs, Ty::int()) => (env, flow))
            (type_expr_as(&env, &flow, &*rhs, Ty::int()) => (env, flow))
            ----------------------------------- ("add")
            (type_expr(env, flow, Expr::Add(lhs, rhs)) => (env, flow, Ty::int()))
        )

        (
            (type_exprs(env, flow, exprs) => (env, flow, tys))
            ----------------------------------- ("tuple")
            (type_expr(env, flow, Expr::Tuple(exprs)) => (env, flow, Ty::tuple(tys)))
        )

        (
            (access_permitted(env, flow, access, &place) => (env, flow))
            (place_ty(&env, &place) => ty)
            (access_ty(&env, access, &place, ty) => ty)
            ----------------------------------- ("share|lease place")
            (type_expr(env, flow, PlaceExpr { access: access @ (Access::Share | Access::Lease), place }) => (&env, &flow, ty))
        )

        (
            (access_permitted(env, flow, access, &place) => (env, flow))
            (place_ty(&env, &place) => ty)
            (give_place(&env, &flow, &place, &ty) => (env, flow))
            ----------------------------------- ("give place")
            (type_expr(env, flow, PlaceExpr { access: access @ Access::Give, place }) => (env, flow, &ty))
        )

        (
            (env.program().class_named(&class_name) => class_decl)
            (class_decl.binder.instantiate_with(&parameters) => ClassDeclBoundData { fields, methods: _ })
            (if fields.len() == exprs.len())
            (let field_tys = fields.into_iter().map(|f| f.ty).collect::<Vec<Ty>>())
            // FIXME: this isn't really right. What we want to do is to first
            // move all call arguments to temporary vars as a unit
            // (which implies some renaming) and THEN do this typing.
            (type_exprs_as(&env, &flow, &exprs, field_tys) => (env, flow))
            ----------------------------------- ("new")
            (type_expr(env, flow, Expr::New(class_name, parameters, exprs)) => (&env, &flow, NamedTy::new(&class_name, &parameters)))
        )

        (
            (type_expr_as(&env, flow, &*cond, TypeName::Int) => (env, flow_cond))
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
    fn give_place(
        env: Env,
        flow: Flow,
        place: Place,
        ty: Ty,
    ) => (Env, Flow) {
        debug(place, ty, env, flow)

        (
            (is_shared(env, ty) => env)
            ----------------------------------- ("shared")
            (give_place(env, flow, _place, ty) => (env, &flow))
        )

        (
            (let flow = flow.move_place(&place))
            ----------------------------------- ("affine")
            (give_place(env, flow, place, _ty) => (&env, flow))
        )
    }
}

judgment_fn! {
    fn access_ty(
        env: Env,
        access: Access,
        place: Place,
        ty: Ty
    ) => Ty {
        debug(access, ty, place, env)

        (
            ----------------------------------- ("give")
            (access_ty(_env, Access::Give, _place, ty) => ty)
        )

        (
            (let perm = Perm::shared(set![place]))
            ----------------------------------- ("share")
            (access_ty(_env, Access::Share, place, ty) => Ty::apply_perm(perm, ty))
        )

        (
            (let perm = Perm::leased(set![place]))
            ----------------------------------- ("share")
            (access_ty(_env, Access::Lease, place, ty) => Ty::apply_perm(perm, ty))
        )
    }
}

judgment_fn! {
    fn type_exprs_as(
        env: Env,
        flow: Flow,
        exprs: Vec<Expr>,
        tys: Vec<Ty>,
    ) => (Env, Flow) {
        debug(exprs, tys, env, flow)

        (
            ----------------------------------- ("none")
            (type_exprs_as(env, flow, (), ()) => (env, flow))
        )

        (
            (type_expr_as(env, flow, expr, ty) => (env, flow))
            (type_exprs_as(env, flow, &exprs, &tys) => (env, flow))
            ----------------------------------- ("cons")
            (type_exprs_as(env, flow, Cons(expr, exprs), Cons(ty, tys)) => (env, flow))
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

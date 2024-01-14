use formality_core::{judgment_fn, set, Cons};

use crate::{
    grammar::{
        Access, ClassDeclBoundData, Expr, FieldDecl, LocalVariableDecl, MethodDecl,
        MethodDeclBoundData, MethodId, NamedTy, Parameter, Perm, Place, PlaceExpr, Predicate,
        ThisDecl, Ty, TypeName, ValueId, Var,
    },
    type_system::{
        accesses::{access_permitted, accesses_permitted},
        blocks::type_block,
        env::Env,
        flow::Flow,
        in_flight::InFlight,
        liveness::LiveVars,
        places::place_ty,
        predicates::prove_predicates,
        subtypes::sub,
    },
};

use super::subtypes::is_shared;

judgment_fn! {
    pub fn can_type_expr_as(
        env: Env,
        flow: Flow,
        live_after: LiveVars,
        expr: Expr,
        as_ty: Ty,
    ) => () {
        debug(expr, as_ty, env, flow, live_after)

        (
            (type_expr_as(env, flow, live_after, expr, as_ty) => _)
            -------------------------------- ("can_type_expr_as")
            (can_type_expr_as(env, flow, live_after, expr, as_ty) => ())
        )
    }
}

judgment_fn! {
    pub fn type_expr_as(
        env: Env,
        flow: Flow,
        live_after: LiveVars,
        expr: Expr,
        as_ty: Ty,
    ) => (Env, Flow) {
        debug(expr, as_ty, env, flow, live_after)

        (
            (type_expr(env, flow, live_after, expr) => (env, flow, ty))
            (sub(env, flow, ty, &as_ty) => (env, flow))
            -------------------------------- ("type_expr_as")
            (type_expr_as(env, flow, live_after, expr, as_ty) => (env, flow))
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
        live_after: LiveVars,
        expr: Expr,
    ) => (Env, Flow, Ty) {
        debug(expr, env, flow, live_after)

        (
            (type_block(env, flow, live_after, block) => (env, flow, ty))
            ----------------------------------- ("block")
            (type_expr(env, flow, live_after, Expr::Block(block)) => (env, flow, ty))
        )

        (
            ----------------------------------- ("constant")
            (type_expr(env, flow, _live_after, Expr::Integer(_)) => (env, flow, Ty::int()))
        )

        (
            (type_expr_as(env, flow, &live_after.before(&*rhs), &*lhs, Ty::int()) => (env, flow))
            (type_expr_as(&env, &flow, &live_after, &*rhs, Ty::int()) => (env, flow))
            ----------------------------------- ("add")
            (type_expr(env, flow, live_after, Expr::Add(lhs, rhs)) => (env, flow, Ty::int()))
        )

        (
            (type_exprs(env, flow, live_after, exprs) => (env, flow, tys))
            ----------------------------------- ("tuple")
            (type_expr(env, flow, live_after, Expr::Tuple(exprs)) => (env, flow, Ty::tuple(tys)))
        )

        (
            (access_permitted(env, flow, live_after, access, &place) => (env, flow))
            (place_ty(&env, &place) => ty)
            (access_ty(&env, access, &place, ty) => ty)
            ----------------------------------- ("share|lease place")
            (type_expr(env, flow, live_after, PlaceExpr { access: access @ (Access::Share | Access::Lease), place }) => (&env, &flow, ty))
        )

        (
            (access_permitted(env, flow, live_after, Access::Give, &place) => (env, flow))
            (place_ty(&env, &place) => ty)
            (give_place(&env, &flow, &place, &ty) => (env, flow))
            ----------------------------------- ("give place")
            (type_expr(env, flow, live_after, PlaceExpr { access: Access::Give, place }) => (env, flow, &ty))
        )

        (
            (env.program().class_named(&class_name) => class_decl)
            (class_decl.binder.instantiate_with(&parameters) => ClassDeclBoundData { fields, methods: _ })
            (if fields.len() == exprs.len())
            // FIXME: what if `parameters` reference variables impacted by moves etc?
            (type_field_exprs_as(&env, &flow, &live_after, &exprs, fields) => (env, flow))

            // After the above judgment, `Temp(0)` represents the "this" value under construction.
            // Map it to `@in_flight`.
            (let env = env.with_place_in_flight(Var::Temp(0)))
            ----------------------------------- ("new")
            (type_expr(env, flow, live_after, Expr::New(class_name, parameters, exprs)) => (&env, &flow, NamedTy::new(&class_name, &parameters)))
        )

        (
            // Start by typing the `this` expression and use that to lookup `method_name`
            (type_expr(env, flow, live_after.before(&exprs), &*receiver) => (env, flow, receiver_ty))
            (resolve_method(&env, &receiver_ty, &method_name, &parameters) => (this_input_ty, inputs, output, predicates))

            // Rename each of the arguments (including `this`) to a temporary variable, with `this` being `temp(0)`.
            (let input_names: Vec<ValueId> = inputs.iter().map(|input| input.name.clone()).collect())
            (let input_temps: Vec<Var> = (1..=inputs.len()).map(|i| Var::Temp(i)).collect())
            (let input_tys: Vec<Ty> = inputs.iter().map(|input| input.ty.clone()).collect())
            (let (this_input_ty, input_tys, output) = (this_input_ty, input_tys, output).with_vars_stored_to(Cons(Var::This, &input_names), Cons(Var::Temp(0), &input_temps)))

            // The self type must match what method expects
            (sub(&env, &flow, &receiver_ty, this_input_ty) => (env, flow))

            // Type each of the method arguments, remapping them to `temp(i)` appropriately as well
            (type_method_arguments_as(&env, &flow, &live_after, &exprs, &input_temps, &input_tys) => (env, flow))

            // Drop all the temporaries
            (accesses_permitted(&env, &flow, &live_after, Access::Drop, Cons(Var::Temp(0), &input_temps)) => (env, flow))

            // Prove predicates
            (prove_predicates(env, &predicates) => env)

            // Rename output variable to in-flight
            (let output = output.with_place_in_flight(Var::Return))
            ----------------------------------- ("call")
            (type_expr(env, flow, live_after, Expr::Call(receiver, method_name, parameters, exprs)) => (&env, &flow, output))
        )

        (
            (type_expr_as(&env, flow, live_after.before_all([&if_true, &if_false]), &*cond, TypeName::Int) => (env, flow_cond))
            (type_expr(&env, &flow_cond, &live_after, &*if_true) => (env, flow_if_true, if_true_ty))
            (type_expr(&env, &flow_cond, &live_after, &*if_false) => (env, flow_if_false, if_false_ty))
            (let flow = flow_if_true.merge(&flow_if_false))
            (env.with(|env| Ok(env.mutual_supertype(&if_true_ty, &if_false_ty))) => (env, ty))
            ----------------------------------- ("if")
            (type_expr(env, flow, live_after, Expr::If(cond, if_true, if_false)) => (&env, &flow, ty))
        )
    }
}

judgment_fn! {
    fn resolve_method(
        env: Env,
        receiver_ty: Ty,
        method_name: MethodId,
        method_parameters: Vec<Parameter>,
    ) => (Ty, Vec<LocalVariableDecl>, Ty, Vec<Predicate>) {
        debug(receiver_ty, method_name, method_parameters, env)

        (
            (if let NamedTy { name: TypeName::Id(class_name), parameters: class_parameters } = &named_ty)!
            (env.program().class_named(&class_name) => class_decl)
            (let ClassDeclBoundData { fields: _, methods } = class_decl.binder.instantiate_with(&class_parameters)?)
            (methods.into_iter().filter(|m| m.name == method_name) => MethodDecl { name: _, binder })
            (let () = tracing::debug!("found method in class {:?}: {:?}", class_name, binder))
            (let MethodDeclBoundData { this: ThisDecl { perm }, inputs, output, predicates, body: _ } = binder.instantiate_with(&method_parameters)?)
            (let this_ty = Ty::apply_perm(perm, &named_ty))
            ----------------------------------- ("class-method")
            (resolve_method(env, named_ty: NamedTy, method_name, method_parameters) => (this_ty, inputs, output, predicates))
        )

        (
            (resolve_method(env, &*ty, method_name, method_parameters) => method_decl)
            ----------------------------------- ("perm")
            (resolve_method(env, Ty::ApplyPerm(_perm, ty), method_name, method_parameters) => method_decl)
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
            (let env = env.with_place_in_flight(&place))
            ----------------------------------- ("affine")
            (give_place(env, flow, place, _ty) => (env, flow))
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
    fn type_field_exprs_as(
        env: Env,
        flow: Flow,
        live_after: LiveVars,
        exprs: Vec<Expr>,
        fields: Vec<FieldDecl>,
    ) => (Env, Flow) {
        debug(exprs, fields, env, flow, live_after)

        (
            ----------------------------------- ("none")
            (type_field_exprs_as(env, flow, _live_after, (), ()) => (env, flow))
        )

        (
            (let FieldDecl { atomic: _, name: field_name, ty: field_ty } = field)

            // "Self" in the class declaration will become the `@temp(0)` value
            (let field_ty = field_ty.with_this_stored_to(Var::Temp(0)))

            // Type the expression and then move `@in_flight` to `@temp(0).<field_name>`
            (type_expr(env, flow, live_after.before(&exprs), expr) => (env, flow, expr_ty))
            (let (env, expr_ty) = (env, expr_ty).with_in_flight_stored_to(Var::Temp(0).dot(&field_name)))
            (let () = tracing::debug!("type_field_exprs_as: expr_ty = {:?} field_ty = {:?} env = {:?}", expr_ty, field_ty, env))

            // The expression type must be a subtype of the field type
            (sub(env, flow, expr_ty, &field_ty) => (env, flow))

            (type_field_exprs_as(env, flow, &live_after, &exprs, &fields) => (env, flow))
            ----------------------------------- ("cons")
            (type_field_exprs_as(env, flow, live_after, Cons(expr, exprs), Cons(field, fields)) => (env, flow))
        )
    }
}

judgment_fn! {
    fn type_method_arguments_as(
        env: Env,
        flow: Flow,
        live_after: LiveVars,
        exprs: Vec<Expr>,
        input_temps: Vec<Var>,
        input_tys: Vec<Ty>,
    ) => (Env, Flow) {
        debug(exprs, input_temps, input_tys, env, flow, live_after)

        (
            ----------------------------------- ("none")
            (type_method_arguments_as(env, flow, _live_after, (), (), ()) => (env, flow))
        )

        (
            // Type the expression and then move `@in_flight` to `@input_temp`
            (type_expr(env, flow, live_after.before(&exprs), expr) => (env, flow, expr_ty))
            (let (env, expr_ty) = (env, expr_ty).with_in_flight_stored_to(&input_temp))
            (let () = tracing::debug!("type_method_arguments_as: expr_ty = {:?} input_temp = {:?} env = {:?}", expr_ty, input_temp, env))

            // The expression type must be a subtype of the field type
            (sub(env, flow, expr_ty, &input_ty) => (env, flow))

            (type_method_arguments_as(env, flow, &live_after, &exprs, &input_temps, &input_tys) => (env, flow))
            ----------------------------------- ("cons")
            (type_method_arguments_as(env, flow, live_after, Cons(expr, exprs), Cons(input_temp, input_temps), Cons(input_ty, input_tys)) => (env, flow))
        )
    }
}
judgment_fn! {
    fn type_exprs_as(
        env: Env,
        flow: Flow,
        live_after: LiveVars,
        exprs: Vec<Expr>,
        tys: Vec<Ty>,
    ) => (Env, Flow) {
        debug(exprs, tys, env, flow, live_after)

        (
            ----------------------------------- ("none")
            (type_exprs_as(env, flow, _live_after, (), ()) => (env, flow))
        )

        (
            (type_expr_as(env, flow, live_after.before(&exprs), expr, ty) => (env, flow))
            (type_exprs_as(env, flow, &live_after, &exprs, &tys) => (env, flow))
            ----------------------------------- ("cons")
            (type_exprs_as(env, flow, live_after, Cons(expr, exprs), Cons(ty, tys)) => (env, flow))
        )
    }
}

judgment_fn! {
    pub fn type_exprs(
        env: Env,
        flow: Flow,
        live_after: LiveVars,
        exprs: Vec<Expr>,
    ) => (Env, Flow, Vec<Ty>) {
        debug(exprs, env, flow, live_after)

        (
            ----------------------------------- ("none")
            (type_exprs(env, flow, _live_after, ()) => (env, flow, ()))
        )

        (
            (type_expr(&env, flow, live_after.before(&tails), head) => (env, flow, head_ty))
            (type_exprs(&env, &flow, &live_after, &tails) => (env, flow, tail_tys))
            ----------------------------------- ("one-or-more")
            (type_exprs(env, flow, live_after, Cons(head, tails)) => (env, flow, Cons(&head_ty, tail_tys)))
        )

    }
}

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
        in_flight::InFlight,
        liveness::LivePlaces,
        predicates::prove_is_copy,
        predicates::prove_predicates,
        subtypes::sub,
    },
};

judgment_fn! {
    pub fn can_type_expr_as(
        env: Env,
        live_after: LivePlaces,
        expr: Expr,
        as_ty: Ty,
    ) => () {
        debug(expr, as_ty, env, live_after)

        (
            (type_expr_as(env, live_after, expr, as_ty) => _)
            -------------------------------- ("can_type_expr_as")
            (can_type_expr_as(env, live_after, expr, as_ty) => ())
        )
    }
}

judgment_fn! {
    pub fn type_expr_as(
        env: Env,
        live_after: LivePlaces,
        expr: Expr,
        as_ty: Ty,
    ) => Env {
        debug(expr, as_ty, env, live_after)

        (
            -------------------------------- ("type_expr_as panic")
            (type_expr_as(env, _live_after, Expr::Panic, _as_ty) => env)
        )

        (
            (type_expr(env, &live_after, expr) => (env, ty))
            (sub(&env, &live_after, ty, &as_ty) => ())
            -------------------------------- ("type_expr_as")
            (type_expr_as(env, live_after, expr, as_ty) => &env)
        )
    }
}

judgment_fn! {
    /// Compute the type of an expression in the given environment.
    /// Requires that the expression is valid in that environment --
    /// i.e., does not access moved state.
    pub fn type_expr(
        env: Env,
        live_after: LivePlaces,
        expr: Expr,
    ) => (Env, Ty) {
        debug(expr, env, live_after)

        (
            (type_block(env, live_after, block) => (env, ty))
            ----------------------------------- ("block")
            (type_expr(env, live_after, Expr::Block(block)) => (env, ty))
        )

        (
            ----------------------------------- ("constant")
            (type_expr(env, _live_after, Expr::Integer(_)) => (env, Ty::int()))
        )

        (
            (type_expr_as(env, &live_after.before(&*rhs), &*lhs, Ty::int()) => env)
            (type_expr_as(&env, &live_after, &*rhs, Ty::int()) => env)
            ----------------------------------- ("add")
            (type_expr(env, live_after, Expr::Add(lhs, rhs)) => (env, Ty::int()))
        )

        (
            (type_exprs(env, live_after, exprs) => (env, tys))
            ----------------------------------- ("tuple")
            (type_expr(env, live_after, Expr::Tuple(exprs)) => (env, Ty::tuple(tys)))
        )

        (
            (access_permitted(env, live_after, access, &place) => env)
            (let ty = env.place_ty(&place)?)
            (access_ty(&env, access, &place, ty) => ty)
            ----------------------------------- ("share|lease place")
            (type_expr(env, live_after, PlaceExpr { access: access @ (Access::Rf | Access::Mt), place }) => (&env, ty))
        )

        (
            (access_permitted(env, &live_after, Access::Mv, &place) => env)
            (let ty = env.place_ty(&place)?)
            (give_place(&env, &live_after, &place, &ty) => env)
            ----------------------------------- ("give place")
            (type_expr(env, live_after, PlaceExpr { access: Access::Mv, place }) => (env, &ty))
        )

        (
            (env.program().class_named(&class_name) => class_decl)
            (let ClassDeclBoundData { predicates, fields, methods: _ } = class_decl.binder.instantiate_with(&parameters)?)
            (if fields.len() == exprs.len())
            (let this_ty = NamedTy::new(&class_name, &parameters))

            (prove_predicates(&env, predicates) => ())

            (let (env, temp_var) = env.push_fresh_variable(&this_ty))

            // FIXME: what if `parameters` reference variables impacted by moves etc?
            (type_field_exprs_as(&env, &live_after, &temp_var, &exprs, &fields) => env)

            // After the above judgment, `Temp(0)` represents the "this" value under construction.
            // Map it to `@in_flight`.
            (let env = env.with_place_in_flight(&temp_var))
            (let env = env.pop_fresh_variable(&temp_var))
            ----------------------------------- ("new")
            (type_expr(env, live_after, Expr::New(class_name, parameters, exprs)) => (&env, &this_ty))
        )

        (
            // Start by typing the `this` expression, store into `@temp(0)`
            (let live_after_receiver = live_after.before(&exprs))
            (type_expr(env, &live_after_receiver, &*receiver) => (env, receiver_ty))
            (let (env, this_var) = env.push_fresh_variable_with_in_flight(&receiver_ty))

            // Use receiver type to look up the method
            (resolve_method(&env, &receiver_ty, &method_name, &parameters) => (this_input_ty, inputs, output, predicates))

            // Rename each of the arguments (including `this`) to a temporary variable, with `this` being `temp(0)`.
            (let input_names: Vec<ValueId> = inputs.iter().map(|input| input.name.clone()).collect())
            (let input_tys: Vec<Ty> = inputs.iter().map(|input| input.ty.clone()).collect())

            // The self type must match what method expects
            (let (this_input_ty, input_tys) = (this_input_ty, input_tys).with_this_stored_to(&this_var))
            (sub(&env, &live_after_receiver, &receiver_ty, this_input_ty) => ())

            // Type each of the method arguments, remapping them to `temp(i)` appropriately as well
            (type_method_arguments_as(&env, &live_after, &exprs, &input_names, &input_tys) => (env, input_temps))

            // Prove predicates
            (prove_predicates(&env, &predicates) => ())

            // Drop all the temporaries
            (accesses_permitted(&env, &live_after, Access::Drop, Cons(&this_var, &input_temps)) => env)
            (let env = env.pop_fresh_variables(Cons(&this_var, &input_temps)))

            // Rename output variable to in-flight
            (let output = output.with_place_in_flight(Var::Return))
            ----------------------------------- ("call")
            (type_expr(env, live_after, Expr::Call(receiver, method_name, parameters, exprs)) => (&env, output))
        )

        (
            (type_expr_as(&env, live_after.before_all([&if_true, &if_false]), &*cond, TypeName::Int) => env)
            (type_expr_as(env, &live_after, &*if_true, Ty::unit()) => env)
            (type_expr_as(env, &live_after, &*if_false, Ty::unit()) => env)
            ----------------------------------- ("if")
            (type_expr(env, live_after, Expr::If(cond, if_true, if_false)) => (env, Ty::unit()))
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
            (let ClassDeclBoundData { predicates: _, fields: _, methods } = class_decl.binder.instantiate_with(&class_parameters)?)
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
        live_after: LivePlaces,
        place: Place,
        ty: Ty,
    ) => Env {
        debug(place, ty, env, live_after)

        (
            (if live_after.is_live(&place))!
            (prove_is_copy(&env, ty) => ())
            ----------------------------------- ("copy")
            (give_place(env, _live_after, _place, ty) => &env)
        )

        (
            (if !live_after.is_live(&place))
            (let env = env.with_place_in_flight(&place))
            ----------------------------------- ("move")
            (give_place(env, live_after, place, _ty) => env)
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
            (access_ty(_env, Access::Mv, _place, ty) => ty)
        )

        (
            (let perm = Perm::rf(set![place]))
            ----------------------------------- ("share")
            (access_ty(_env, Access::Rf, place, ty) => Ty::apply_perm(perm, ty.strip_perm()))
        )

        (
            (let perm = Perm::mt(set![place]))
            ----------------------------------- ("share")
            (access_ty(_env, Access::Mt, place, ty) => Ty::apply_perm(perm, ty.strip_perm()))
        )
    }
}

judgment_fn! {
    fn type_field_exprs_as(
        env: Env,
        live_after: LivePlaces,
        temp_var: Var,
        exprs: Vec<Expr>,
        fields: Vec<FieldDecl>,
    ) => Env {
        debug(temp_var, exprs, fields, env, live_after)

        (
            ----------------------------------- ("none")
            (type_field_exprs_as(env, _live_after, _temp, (), ()) => env)
        )

        (
            (let FieldDecl { atomic: _, name: field_name, ty: field_ty } = field)

            // "Self" in the class declaration will become the `@temp(0)` value
            (let field_ty = field_ty.with_this_stored_to(&temp_var))

            // Type the expression and then move `@in_flight` to `@temp(0).<field_name>`
            (let live_after_expr = live_after.before(&exprs))
            (type_expr(env, &live_after_expr, expr) => (env, expr_ty))
            (let (env, expr_ty) = (env, expr_ty).with_in_flight_stored_to(temp_var.dot(&field_name)))
            (let () = tracing::debug!("type_field_exprs_as: expr_ty = {:?} field_ty = {:?} env = {:?}", expr_ty, field_ty, env))

            // The expression type must be a subtype of the field type
            (sub(&env, &live_after_expr, expr_ty, &field_ty) => ())

            (type_field_exprs_as(&env, &live_after, &temp_var, &exprs, &fields) => env)
            ----------------------------------- ("cons")
            (type_field_exprs_as(env, live_after, temp_var, Cons(expr, exprs), Cons(field, fields)) => env)
        )
    }
}

judgment_fn! {
    fn type_method_arguments_as(
        env: Env,
        live_after: LivePlaces,
        exprs: Vec<Expr>,
        input_names: Vec<ValueId>,
        input_tys: Vec<Ty>,
    ) => (Env, Vec<Var>) {
        debug(exprs, input_names, input_tys, env, live_after)

        (
            ----------------------------------- ("none")
            (type_method_arguments_as(env, _live_after, (), (), ()) => (env, ()))
        )

        (
            // Type the expression and then move `@in_flight` to `@input_temp`
            (let live_after_expr = live_after.before(&exprs))
            (type_expr(env, &live_after_expr, expr) => (env, expr_ty))
            (let (env, input_temp) = env.push_fresh_variable_with_in_flight(&expr_ty))
            (let () = tracing::debug!("type_method_arguments_as: expr_ty = {:?} input_temp = {:?} env = {:?}", expr_ty, input_temp, env))

            // The expression type must be a subtype of the field type
            (let input_ty = input_ty.with_var_stored_to(&input_name, &input_temp))
            (sub(&env, &live_after_expr, expr_ty, &input_ty) => ())

            (let input_tys = input_tys.with_var_stored_to(&input_name, &input_temp))
            (type_method_arguments_as(&env, &live_after, &exprs, &input_names, &input_tys) => (env, input_temps))
            ----------------------------------- ("cons")
            (type_method_arguments_as(
                env,
                live_after,
                Cons(expr, exprs),
                Cons(input_name, input_names),
                Cons(input_ty, input_tys),
            ) => (env, Cons(&input_temp, input_temps)))
        )
    }
}
judgment_fn! {
    fn type_exprs_as(
        env: Env,
        live_after: LivePlaces,
        exprs: Vec<Expr>,
        tys: Vec<Ty>,
    ) => Env {
        debug(exprs, tys, env, live_after)

        (
            ----------------------------------- ("none")
            (type_exprs_as(env, _live_after, (), ()) => env)
        )

        (
            (type_expr_as(env, live_after.before(&exprs), expr, ty) => env)
            (type_exprs_as(env, &live_after, &exprs, &tys) => env)
            ----------------------------------- ("cons")
            (type_exprs_as(env, live_after, Cons(expr, exprs), Cons(ty, tys)) => env)
        )
    }
}

judgment_fn! {
    pub fn type_exprs(
        env: Env,
        live_after: LivePlaces,
        exprs: Vec<Expr>,
    ) => (Env, Vec<Ty>) {
        debug(exprs, env, live_after)

        (
            ----------------------------------- ("none")
            (type_exprs(env, _live_after, ()) => (env, ()))
        )

        (
            (type_expr(&env, live_after.before(&tails), head) => (env, head_ty))
            (type_exprs(&env, &live_after, &tails) => (env, tail_tys))
            ----------------------------------- ("one-or-more")
            (type_exprs(env, live_after, Cons(head, tails)) => (env, Cons(&head_ty, tail_tys)))
        )

    }
}

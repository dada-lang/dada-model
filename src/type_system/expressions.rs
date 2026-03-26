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
        pop_normalize::normalize_ty_for_pop,
        predicates::{
            prove_is_copy, prove_is_move, prove_is_mut, prove_is_shareable, prove_predicates,
        },
        subtypes::sub,
        types::check_type,
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
            (type_expr(env, live_after, expr) => (env, ty))
            (sub(env, live_after, ty, as_ty) => ())
            -------------------------------- ("type_expr_as")
            (type_expr_as(env, live_after, expr, as_ty) => env)
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
            ----------------------------------- ("true")
            (type_expr(env, _live_after, Expr::True) => (env, Ty::bool()))
        )

        (
            ----------------------------------- ("false")
            (type_expr(env, _live_after, Expr::False) => (env, Ty::bool()))
        )

        // Arithmetic: Int × Int → Int
        (
            (if op.is_arithmetic())!
            (type_expr_as(env, live_after.before(&**rhs), &**lhs, Ty::int()) => env)
            (type_expr_as(env, live_after, &**rhs, Ty::int()) => env)
            ----------------------------------- ("arithmetic")
            (type_expr(env, live_after, Expr::BinaryOp(lhs, op, rhs)) => (env, Ty::int()))
        )

        // Comparison: Int × Int → Bool
        (
            (if op.is_comparison())!
            (type_expr_as(env, live_after.before(&**rhs), &**lhs, Ty::int()) => env)
            (type_expr_as(env, live_after, &**rhs, Ty::int()) => env)
            ----------------------------------- ("comparison")
            (type_expr(env, live_after, Expr::BinaryOp(lhs, op, rhs)) => (env, Ty::bool()))
        )

        (
            (type_exprs(env, live_after, exprs) => (env, tys))
            ----------------------------------- ("tuple")
            (type_expr(env, live_after, Expr::Tuple(exprs)) => (env, Ty::tuple(tys)))
        )

        (
            ----------------------------------- ("size_of")
            (type_expr(env, _live_after, Expr::SizeOf(_parameters)) => (env, Ty::int()))
        )

        // Array operations
        (
            (let (array_ty, _element_ty) = NamedTy::array(parameters)?)
            (type_expr_as(env, live_after, &**length, Ty::int()) => env)
            ----------------------------------- ("array_new")
            (type_expr(env, live_after, Expr::ArrayNew(parameters, length)) => (env, array_ty))
        )

        (
            (let (array_named_ty, _element_ty, perm_a) = NamedTy::array_with_a(parameters)?)
            (let expected_ty: Ty = Ty::apply_perm(perm_a, array_named_ty))
            (type_expr_as(env, live_after, &**array, expected_ty) => env)
            ----------------------------------- ("array_capacity")
            (type_expr(env, live_after, Expr::ArrayCapacity(parameters, array)) => (env.clone(), Ty::int()))
        )

        (
            (let (array_named_ty, element_ty, perm_p, perm_a) = NamedTy::array_with_pa(parameters)?)
            (let expected_array_ty: Ty = Ty::apply_perm(perm_a, array_named_ty))
            (type_expr_as(env, live_after.before(&**index), &**array, expected_array_ty) => env)
            (type_expr_as(env, live_after, &**index, Ty::int()) => env)
            (let result_ty: Ty = Ty::apply_perm(perm_p, element_ty))
            ----------------------------------- ("array_give")
            (type_expr(env, live_after, Expr::ArrayGive(parameters, array, index)) => (env, result_ty))
        )

        (
            (let (array_named_ty, _element_ty, _perm_p, perm_a) = NamedTy::array_with_pa(parameters)?)
            (let expected_array_ty: Ty = Ty::apply_perm(perm_a, array_named_ty))
            (type_expr_as(env, live_after.before(&**from).before(&**to), &**array, expected_array_ty) => env)
            (type_expr_as(env, live_after.before(&**to), &**from, Ty::int()) => env)
            (type_expr_as(env, live_after, &**to, Ty::int()) => env)
            ----------------------------------- ("array_drop")
            (type_expr(env, live_after, Expr::ArrayDrop(parameters, array, from, to)) => (env, Ty::unit()))
        )

        (
            (let (array_named_ty, element_ty, perm_a) = NamedTy::array_with_a(parameters)?)
            (let expected_array_ty: Ty = Ty::apply_perm(perm_a, array_named_ty))
            (prove_is_mut(env, perm_a) => ())
            (type_expr_as(env, live_after.before(&**index).before(&**value), &**array, expected_array_ty) => env)
            (type_expr_as(env, live_after.before(&**value), &**index, Ty::int()) => env)
            (type_expr_as(env, live_after, &**value, element_ty) => env)
            ----------------------------------- ("array_write")
            (type_expr(env, live_after, Expr::ArrayWrite(parameters, array, index, value)) => (env, Ty::unit()))
        )

        (
            (type_expr(env, live_after, &**expr) => (env, ty))
            (prove_is_shareable(env, ty) => ())
            ----------------------------------- ("share expr")
            (type_expr(env, live_after, Expr::Share(expr)) => (env, Ty::apply_perm(Perm::Shared, ty)))
        )

        // is_last_ref[A](value) — returns Bool
        // A must be a ref permission. Value is typed as A T for some T.
        (
            (type_expr(env, live_after, &**value) => (env, _value_ty))
            ----------------------------------- ("is_last_ref")
            (type_expr(env, live_after, Expr::IsLastRef(_parameters, value)) => (env, Ty::bool()))
        )

        (
            // Must not be conflicting permissions in the environment.
            (access_permitted(env, live_after, Access::Rf, place) => env)

            // Resulting type is `ref[place]` with the underlying object type.
            (let ty_place = env.place_ty(place)?)
            (let ty = Ty::apply_perm(Perm::rf(set![place]), ty_place.strip_perm()))
            ----------------------------------- ("ref place")
            (type_expr(env, live_after, PlaceExpr { access: Access::Rf, place }) => (env, ty))
        )

        (
            (access_permitted(env, live_after, Access::Mt, place) => env)

            // You can only apply `.mut` to places that you have unique access to.
            (let ty_place = env.place_ty(place)?)
            (prove_is_move(env, ty_place) => ())

            // Resulting type is `mut[place]` with the underlying object type.
            (let ty = Ty::apply_perm(Perm::mt(set![place]), ty_place.strip_perm()))
            ----------------------------------- ("mut place")
            (type_expr(env, live_after, PlaceExpr { access: Access::Mt, place }) => (env, ty))
        )

        (
            (access_permitted(env, live_after, Access::Gv, place) => env)
            (let ty = env.place_ty(place)?)
            (move_place(env, live_after, place, ty) => env)
            ----------------------------------- ("give place")
            (type_expr(env, live_after, PlaceExpr { access: Access::Gv, place }) => (env, ty))
        )

        (
            (access_permitted(env, live_after, Access::Drop, place) => env)
            (let ty = env.place_ty(place)?)
            (move_place(env, live_after, place, ty) => env)
            ----------------------------------- ("drop place")
            (type_expr(env, live_after, PlaceExpr { access: Access::Drop, place }) => (env, Ty::unit()))
        )

        (
            // Find the class definition
            (let class_decl = env.program().class_named(class_name)?)

            // Extract the class predicates along with the fields and their types.
            (let ClassDeclBoundData { predicates, fields, methods: _, drop_body: _ } = class_decl.binder.instantiate_with(parameters)?)

            // Check we have the correct number of arguments.
            (if fields.len() == exprs.len())

            // Prove that the class requirements hold.
            (let this_ty = NamedTy::new(class_name, parameters))
            (prove_predicates(env, predicates) => ())

            (let (env, temp_var) = env.push_fresh_variable(this_ty))

            // FIXME: what if `parameters` reference variables impacted by moves etc?
            (type_field_exprs_as(env, live_after, temp_var, exprs, fields) => env)

            // After the above judgment, `Temp(0)` represents the "this" value under construction.
            // Map it to `@in_flight`.
            (let env = env.with_place_in_flight(temp_var))
            (let env = env.pop_fresh_variable(temp_var))
            ----------------------------------- ("new")
            (type_expr(env, live_after, Expr::New(class_name, parameters, exprs)) => (env, this_ty))
        )

        (
            // Start by typing the `this` expression, store into `@temp(0)`
            (let live_after_receiver = live_after.before(exprs))
            (type_expr(env, live_after_receiver, &**receiver) => (env, receiver_ty))
            (let (env, this_var) = env.push_fresh_variable_with_in_flight(receiver_ty))

            // Use receiver type to look up the method
            (resolve_method(env, receiver_ty, method_name, parameters) => (this_input_ty, inputs, output, predicates))

            // Rename each of the arguments (including `this`) to a temporary variable, with `this` being `temp(0)`.
            (let input_names: Vec<ValueId> = inputs.iter().map(|input| input.name.clone()).collect())
            (let input_tys: Vec<Ty> = inputs.iter().map(|input| input.ty.clone()).collect())

            // The self type must match what method expects.
            // Also rename output's `self` references to this_var.
            (let (this_input_ty, input_tys, output) = (this_input_ty.clone(), input_tys.clone(), output.clone()).with_this_stored_to(this_var))
            (sub(env, live_after_receiver, receiver_ty, this_input_ty) => ())

            // Type each of the method arguments, remapping them to `temp(i)` appropriately as well.
            // Also thread output through to rename named parameter references.
            (type_method_arguments_as(env, live_after, exprs, (this_var,), input_names, input_tys, output) => (env, input_temps, output))

            // Prove predicates
            (prove_predicates(env, predicates) => ())

            // Normalize output before popping (env still has all bindings for fresh vars).
            // This resolves place-based permissions referencing the about-to-be-popped temporaries.
            (let pre_norm_output = output.clone())
            (let output = normalize_ty_for_pop(&env, &live_after, &output, &input_temps)?)

            // Sanity check: normalization only weakens (strips dead links, Rfd→Shared),
            // so the original output must be a subtype of the normalized result.
            // If this fails, our normalization rules are buggy — not a user error.
            (let () = assert!(sub(&env, &live_after, &pre_norm_output, &output).is_proven(),
                "normalization soundness check failed: {:?} is not a subtype of {:?}", pre_norm_output, output))

            // Validate the normalized output in the current env (still has fresh vars).
            (check_type(env, output) => ())

            // Drop all the temporaries
            (accesses_permitted(env, live_after, Access::Drop, input_temps) => env)
            (let env = env.pop_fresh_variables(input_temps))

            // Rename output variable to in-flight
            (let output = output.with_place_in_flight(Var::Return))
            ----------------------------------- ("call")
            (type_expr(env, live_after, Expr::Call(receiver, method_name, parameters, exprs)) => (env, output))
        )

        (
            (type_expr_as(env, live_after.before_all([if_true, if_false]), &**cond, TypeName::Bool) => env)
            (type_expr_as(env, live_after, &**if_true, Ty::unit()) => env)
            (type_expr_as(env, live_after, &**if_false, Ty::unit()) => env)
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
            (let class_decl = env.program().class_named(class_name)?)
            (let ClassDeclBoundData { predicates: _, fields: _, methods, drop_body: _ } = class_decl.binder.instantiate_with(class_parameters)?)
            (MethodDecl { name: _, binder } in methods.into_iter().filter(|m| m.name == *method_name))
            (let () = tracing::debug!("found method in class {:?}: {:?}", class_name, binder))
            (let MethodDeclBoundData { this: ThisDecl { perm }, inputs, output, predicates, body: _ } = binder.instantiate_with(method_parameters)?)
            (let this_ty = Ty::apply_perm(perm, named_ty))
            ----------------------------------- ("class-method")
            (resolve_method(env, named_ty: NamedTy, method_name, method_parameters) => (this_ty, inputs, output, predicates))
        )

        (
            (resolve_method(env, &**ty, method_name, method_parameters) => method_decl)
            ----------------------------------- ("perm")
            (resolve_method(env, Ty::ApplyPerm(_perm, ty), method_name, method_parameters) => method_decl)
        )
    }
}

judgment_fn! {
    fn move_place(
        env: Env,
        live_after: LivePlaces,
        place: Place,
        ty: Ty,
    ) => Env {
        debug(place, ty, env, live_after)

        (
            (if live_after.is_live(place))!
            (prove_is_copy(env, ty) => ())
            ----------------------------------- ("copy")
            (move_place(env, _live_after, _place, ty) => env)
        )

        (
            (if !live_after.is_live(place))
            (let env = env.with_place_in_flight(place))
            ----------------------------------- ("give")
            (move_place(env, live_after, place, _ty) => env)
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
            (access_ty(_env, Access::Gv, _place, ty) => ty)
        )

        (
            (let perm = Perm::rf(set![place]))
            ----------------------------------- ("ref")
            (access_ty(_env, Access::Rf, place, ty) => Ty::apply_perm(perm, ty.strip_perm()))
        )

        (
            (let perm = Perm::mt(set![place]))
            ----------------------------------- ("mut")
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
            (let field_ty = field_ty.with_this_stored_to(temp_var))

            // Type the expression and then move `@in_flight` to `@temp(0).<field_name>`
            (let live_after_expr = live_after.before(exprs))
            (type_expr(env, live_after_expr, expr) => (env, expr_ty))
            (let (env, expr_ty) = (env.clone(), expr_ty.clone()).with_in_flight_stored_to(temp_var.dot(field_name)))
            (let () = tracing::debug!("type_field_exprs_as: expr_ty = {:?} field_ty = {:?} env = {:?}", expr_ty, field_ty, env))

            // The expression type must be a subtype of the field type
            (sub(env, live_after_expr, expr_ty, field_ty) => ())

            (type_field_exprs_as(env, live_after, temp_var, exprs, fields) => env)
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
        input_temps: Vec<Var>,
        input_names: Vec<ValueId>,
        input_tys: Vec<Ty>,
        output: Ty,
    ) => (Env, Vec<Var>, Ty) {
        debug(exprs, input_temps, input_names, input_tys, output, env, live_after)

        (
            ----------------------------------- ("none")
            (type_method_arguments_as(env, _live_after, (), temps, (), (), output) => (env, temps, output))
        )

        (
            // Liveness is tricky here
            //
            // ```
            // expr_0.call(expr_1, ..., expr_n)
            // ```
            //
            // becomes effectively
            //
            // ```
            // // expr_0..expr_n are live
            // tmp_0 = expr_0
            // // tmp_0 and expr_1..expr_n are live
            // tmp_1 = expr_1
            // ...
            // // tmp_0..tmp_(n-1) and expr_n are live
            // tmp_n = expr_n
            // // tmp_0 .. tmp_n is live here
            // call(tmp_0, ..., tmp_n)
            // ```
            //
            // When we are checking `expr_i`, each `expr_j` where `j > i` is yet to be evaluated.
            //
            //

            // Type the expression and then move `@in_flight` to `@input_temp`
            (let live_after_expr = live_after.before(exprs).before_all(input_temps))
            (type_expr(env, live_after_expr, expr) => (env, expr_ty))
            (let (env, input_temp) = env.push_fresh_variable_with_in_flight(expr_ty))
            (let () = tracing::debug!("type_method_arguments_as: expr_ty = {:?} input_temp = {:?} env = {:?}", expr_ty, input_temp, env))

            // The expression type must be a subtype of the field type
            (let input_ty = input_ty.with_var_stored_to(input_name, input_temp))
            (sub(env, live_after_expr, expr_ty, input_ty) => ())

            // Also rename in remaining input types and the output type
            (let input_tys = input_tys.with_var_stored_to(input_name, input_temp))
            (let output = output.with_var_stored_to(input_name, input_temp))
            (type_method_arguments_as(env, live_after, exprs, Cons(input_temp, input_temps), input_names, input_tys, output) => triple)
            ----------------------------------- ("cons")
            (type_method_arguments_as(
                env,
                live_after,
                Cons(expr, exprs),
                input_temps,
                Cons(input_name, input_names),
                Cons(input_ty, input_tys),
                output,
            ) => triple)
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
            (type_expr_as(env, live_after.before(exprs), expr, ty) => env)
            (type_exprs_as(env, live_after, exprs, tys) => env)
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
            (type_expr(env, live_after.before(tails), head) => (env, head_ty))
            (type_exprs(env, live_after, tails) => (env, tail_tys))
            ----------------------------------- ("one-or-more")
            (type_exprs(env, live_after, Cons(head, tails)) => (env, Cons(head_ty, tail_tys)))
        )

    }
}

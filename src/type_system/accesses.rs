use formality_core::{judgment_fn, Cons, Set};

use crate::{
    dada_lang::grammar::Variable,
    grammar::{Access, FieldDecl, NamedTy, Parameter, Perm, Place, Ty, Var},
    type_system::{
        env::Env,
        flow::Flow,
        liveness::LiveVars,
        places::{place_fields, place_ty},
        quantifiers::fold,
    },
};

judgment_fn! {
    /// Convenience rule for applying same access to multiple places.
    pub fn accesses_permitted(
        env: Env,
        flow: Flow,
        live_after: LiveVars,
        access: Access,
        places: Vec<Place>,
    ) => (Env, Flow) {
        debug(access, places, env, flow, live_after)

        (
            (fold((env, flow), places, &|(env, flow), place| {
                access_permitted(env, flow, &live_after, &access, place)
            }) => (env, flow))
            -------------------------------- ("accesses_permitted")
            (accesses_permitted(env, flow, live_after, access, places) => (env, flow))
        )
    }
}

judgment_fn! {
    /// True if `place` is initialized and
    /// accessing it in the fashion given by `access` is permitted
    /// by the other variables in the environment.
    pub fn access_permitted(
        env: Env,
        flow: Flow,
        live_after: LiveVars,
        access: Access,
        place: Place,
    ) => (Env, Flow) {
        debug(access, place, env, flow, live_after)

        (
            (if !flow.is_moved(&place))
            (env_permits_access(env, flow, live_after, access, place) => (env, flow))
            -------------------------------- ("access_permitted")
            (access_permitted(env, flow, live_after, access, place) => (env, flow))
        )
    }
}

judgment_fn! {
    /// True if accessing `place` in the fashion given by `access`
    /// is permitted by the other variables in the environment.
    /// **Does not check if `place` is initialized.**
    /// This is because this judgment is used as part of assignments.
    pub fn env_permits_access(
        env: Env,
        flow: Flow,
        live_after: LiveVars,
        access: Access,
        place: Place,
    ) => (Env, Flow) {
        debug(access, place, env, flow, live_after)

        (
            (let live_var_tys: Vec<Ty> = live_after.vars().iter().map(|var| env.var_ty(var).unwrap()).cloned().collect())
            (parameters_permit_access(env, flow, live_var_tys, &access, &place) => (env, flow))
            (accessed_place_permits_access(env, flow, &live_after, access, &place) => (env, flow))
            -------------------------------- ("env_permits_access")
            (env_permits_access(env, flow, live_after, access, place) => (env, flow))
        )
    }
}

judgment_fn! {
    fn parameters_permit_access(
        env: Env,
        flow: Flow,
        parameters: Vec<Parameter>,
        access: Access,
        place: Place,
    ) => (Env, Flow) {
        debug(parameters, access, place, env, flow)

        (
            -------------------------------- ("nil")
            (parameters_permit_access(env, flow, (), _access, _place) => (env, flow))
        )


        (
            (parameter_permits_access(env, flow, parameter, access, &place) => (env, flow))
            (parameters_permit_access(env, flow, &parameters, access, &place) => (env, flow))
            -------------------------------- ("cons")
            (parameters_permit_access(env, flow, Cons(parameter, parameters), access, place) => (env, flow))
        )
    }
}

judgment_fn! {
    fn parameter_permits_access(
        env: Env,
        flow: Flow,
        parameter: Parameter,
        access: Access,
        place: Place,
    ) => (Env, Flow) {
        debug(parameter, access, place, env, flow)

        (
            (ty_permits_access(env, flow, ty, access, place) => (env, flow))
            -------------------------------- ("ty")
            (parameter_permits_access(env, flow, Parameter::Ty(ty), access, place) => (env, flow))
        )

        (
            (perm_permits_access(env, flow, perm, access, place) => (env, flow))
            -------------------------------- ("perm")
            (parameter_permits_access(env, flow, Parameter::Perm(perm), access, place) => (env, flow))
        )
    }
}

judgment_fn! {
    pub fn ty_permits_access(
        env: Env,
        flow: Flow,
        ty: Ty,
        access: Access,
        place: Place,
    ) => (Env, Flow) {
        debug(ty, access, place, env, flow)

        (
            (parameters_permit_access(env, flow, parameters, access, place) => (env, flow))
            -------------------------------- ("ty")
            (ty_permits_access(env, flow, NamedTy { name: _, parameters }, access, place) => (env, flow))
        )

        (
            (perm_permits_access(env, flow, perm, access, &place) => (env, flow))
            (ty_permits_access(env, flow, &*ty, access, &place) => (env, flow))
            -------------------------------- ("ty")
            (ty_permits_access(env, flow, Ty::ApplyPerm(perm, ty), access, place) => (env, flow))
        )

        (
            // FIXME: check the variables visible by `v` and allow access only if place is not one of those
            -------------------------------- ("universal")
            (ty_permits_access(env, flow, Variable::UniversalVar(_), _access, _place) => (env, flow))
        )
    }
}

judgment_fn! {
    fn perm_permits_access(
        env: Env,
        flow: Flow,
        perm: Perm,
        access: Access,
        place: Place,
    ) => (Env, Flow) {
        debug(perm, access, place, env, flow)

        (
            -------------------------------- ("my")
            (perm_permits_access(env, flow, Perm::My, _access, _place) => (env, flow))
        )

        // If the place being accessed is different from the place that was borrowed,
        // that is fine, no matter what kind of access it is.
        (
            (if place_disjoint_from_all_of(&accessed_place, &perm_places))
            (perm_places_permit_access(env, flow, perm_places, access, accessed_place) => (env, flow))
            -------------------------------- ("disjoint")
            (perm_permits_access(env, flow, Perm::Shared(perm_places) | Perm::Leased(perm_places) | Perm::Given(perm_places), access, accessed_place) => (env, flow))
        )

        (
            (if place_disjoint_from_or_prefix_of_all_of(&given_place, &perm_places))
            (perm_places_permit_access(env, flow, perm_places, access, given_place) => (env, flow))
            -------------------------------- ("disjoint-or-prefix")
            (perm_permits_access(env, flow, Perm::Shared(perm_places) | Perm::Leased(perm_places) | Perm::Given(perm_places), Access::Give, given_place) => (env, flow))
        )

        // If this is a shared access, and the borrow was a shared borrow, that's fine.
        (
            (perm_places_permit_access(env, flow, perm_places, Access::Share, accessed_place) => (env, flow))
            -------------------------------- ("shared-shared")
            (perm_permits_access(env, flow, Perm::Shared(perm_places), Access::Share, accessed_place) => (env, flow))
        )

        (
            // FIXME: check the variables visible by `v` and allow access only if place is not one of those
            -------------------------------- ("universal")
            (perm_permits_access(env, flow, Variable::UniversalVar(_), _access, _place) => (env, flow))
        )
    }
}

judgment_fn! {
    fn perm_places_permit_access(
        env: Env,
        flow: Flow,
        perm_places: Set<Place>,
        access: Access,
        place: Place,
    ) => (Env, Flow) {
        debug(perm_places, access, place, env, flow)

        (
            -------------------------------- ("nil")
            (perm_places_permit_access(env, flow, (), _access, _place) => (env, flow))
        )

        (
            (place_ty(&env, perm_place) => ty)
            (ty_permits_access(&env, &flow, ty, access, &place) => (env, flow))
            (perm_places_permit_access(env, flow, &perm_places, access, &place) => (env, flow))
            -------------------------------- ("nil")
            (perm_places_permit_access(env, flow, Cons(perm_place, perm_places), access, place) => (env, flow))
        )

        (
            (perm_places_permit_access(env, flow, &perm_places, access, &place) => (env, flow))
            -------------------------------- ("nil")
            (perm_places_permit_access(env, flow, Cons(Place { var: Var::InFlight, projections: _ }, perm_places), access, place) => (env, flow))
        )
    }
}

/// True if `accessed_place` is disjoint from each place in `perm_places`.
/// Disjoint means that the two places are not the same place nor are they overlapping.
/// For example, `x` is disjoint from `y` and `x.f` is disjoint from `x.g`,
/// but `x.f` is not disjoint from `x.f.g` (nor vice versa).
fn place_disjoint_from_all_of(accessed_place: &Place, perm_places: &Set<Place>) -> bool {
    perm_places
        .iter()
        .all(|place| accessed_place.is_disjoint_from(place))
}

/// True if `accessed_place` is either (a) disjoint from or (b) a prefix of each place in `perm_places`.
/// This is similar to `place_disjoint_from_all_of` except that it would permit
/// an `accessed_place` like `x.f` and a `perm_place` like `x.f.g` (but not vice versa).
/// This is used when giving values: it's ok to have `x.f.give` even if there is a share of
/// `x.f.g`, we can rewrite that to share to `@in_flight.g`.
fn place_disjoint_from_or_prefix_of_all_of(
    accessed_place: &Place,
    perm_places: &Set<Place>,
) -> bool {
    perm_places
        .iter()
        .all(|place| accessed_place.is_disjoint_from(place) || accessed_place.is_prefix_of(place))
}

judgment_fn! {
    fn accessed_place_permits_access(
        env: Env,
        flow: Flow,
        live_after: LiveVars,
        access: Access,
        place: Place,
    ) => (Env, Flow) {
        debug(place, access, env, flow, live_after)

        (
            (if !live_after.is_live(&place.var))!
            --------------------------------- ("not live")
            (accessed_place_permits_access(env, flow, live_after, _access, place) => (env, flow))
        )

        (
            (if live_after.is_live(&place.var))!
            (let place_prefixes = place.strict_prefixes())
            (fold((env, flow), place_prefixes, &|(env, flow), place_prefix| {
                accessed_place_prefix_permits_access(env, flow, place_prefix, access, &place)
            }) => (env, flow))
            --------------------------------- ("live")
            (accessed_place_permits_access(env, flow, live_after, access, place) => (env, flow))
        )
    }
}

judgment_fn! {
    fn accessed_place_prefix_permits_access(
        env: Env,
        flow: Flow,
        place_prefix: Place,
        access: Access,
        place: Place,
    ) => (Env, Flow) {
        debug(place_prefix, place, access, env, flow)
        assert(place_prefix.is_strict_prefix_of(&place))

        (
            (place_fields(&env, &place_prefix) => fields)
            (fold((&env, &flow), fields, &|(env, flow), field| {
                field_of_accessed_place_prefix_permits_access(env, flow, &place_prefix, field, access, &place)
            }) => (env, flow))
            --------------------------------- ("live")
            (accessed_place_prefix_permits_access(env, flow, place_prefix, access, place) => (env, flow))
        )
    }
}

judgment_fn! {
    fn field_of_accessed_place_prefix_permits_access(
        env: Env,
        flow: Flow,
        place_prefix: Place,
        field: FieldDecl,
        access: Access,
        place: Place,
    ) => (Env, Flow) {
        debug(place_prefix, field, place, access, env, flow)
        assert(place_prefix.is_strict_prefix_of(&place))

        (
            (let place_with_field = place_prefix.project(&field.name))
            (if !place_with_field.is_prefix_of(&place))!

            // Subtle: treat GIVE as DROP here. This means that if the user is giving `foo.bar`,
            // then we don't allow a share of (say) `foo.bar.baz`. Ordinarily this would be ok
            // because we could track the new name, but when the share is coming from a field
            // inside the struct, we can't update those types as they live in the field declaration
            // and not the environment. So we treat GIVE as a DROP, which does not track new locations.
            (ty_permits_access(env, flow, field.ty, access.give_to_drop(), place) => (env, flow))
            --------------------------------- ("not accessed place")
            (field_of_accessed_place_prefix_permits_access(env, flow, place_prefix, field, access, place) => (env, flow))
        )


        (
            (let place_with_field = place_prefix.project(&field.name))
            (if place_with_field.is_prefix_of(&place))!
            --------------------------------- ("is accessed place")
            (field_of_accessed_place_prefix_permits_access(env, flow, place_prefix, field, _access, place) => (env, flow))
        )
    }
}

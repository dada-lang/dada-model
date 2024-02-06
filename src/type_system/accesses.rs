use formality_core::{judgment_fn, Cons};

use crate::{
    grammar::{Access, FieldDecl, Parameter, Place, Ty},
    type_system::{
        env::Env,
        flow::Flow,
        liveness::LiveVars,
        places::place_fields,
        quantifiers::{fold, for_all},
        terms::{terms, Terms},
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
    pub fn parameter_permits_access(
        env: Env,
        flow: Flow,
        parameter: Parameter,
        access: Access,
        place: Place,
    ) => (Env, Flow) {
        debug(parameter, access, place, env, flow)

        (
            (terms(env, p) => (env, terms))
            (terms_permit_access(env, &flow, terms, access, &place) => (env, flow))
            -------------------------------- ("ty")
            (parameter_permits_access(env, flow, p, access, place) => (env, flow))
        )
    }
}

judgment_fn! {
    fn terms_permit_access(
        env: Env,
        flow: Flow,
        terms: Terms,
        access: Access,
        accessed_place: Place,
    ) => (Env, Flow) {
        debug(terms, access, accessed_place, env, flow)

        (
            (let Terms { unique: _, shared: _, leased: _, vars: _, named_tys: _, shared_places, leased_places } = terms)
            (for_all(shared_places, &|shared_place| shared_place_permits_access(shared_place, access, &accessed_place)) => ())
            (for_all(&leased_places, &|leased_place| leased_place_permits_access(leased_place, access, &accessed_place)) => ())
            -------------------------------- ("terms")
            (terms_permit_access(env, flow, terms, access, accessed_place) => (&env, &flow))
        )
    }
}

judgment_fn! {
    fn shared_place_permits_access(
        shared_place: Place,
        access: Access,
        accessed_place: Place,
    ) => () {
        debug(shared_place, access, accessed_place)

        (

            -------------------------------- ("share-share")
            (shared_place_permits_access(_shared_place, Access::Share, _accessed_place) => ())
        )

        (
            (if place_disjoint_from(&accessed_place, &shared_place))
            -------------------------------- ("share-mutation")
            (shared_place_permits_access(shared_place, Access::Lease | Access::Drop, accessed_place) => ())
        )

        (
            (if place_disjoint_from_or_prefix_of(&accessed_place, &shared_place))
            -------------------------------- ("share-give")
            (shared_place_permits_access(shared_place, Access::Give, accessed_place) => ())
        )
    }
}

judgment_fn! {
    fn leased_place_permits_access(
        leased_place: Place,
        access: Access,
        accessed_place: Place,
    ) => () {
        debug(leased_place, access, accessed_place)

        (
            (if place_disjoint_from(&accessed_place, &leased_place))
            -------------------------------- ("lease-mutation")
            (leased_place_permits_access(leased_place, Access::Share | Access::Lease | Access::Drop, accessed_place) => ())
        )

        (
            (if place_disjoint_from_or_prefix_of(&accessed_place, &leased_place))
            -------------------------------- ("lease-give")
            (leased_place_permits_access(leased_place, Access::Give, accessed_place) => ())
        )
    }
}

fn place_disjoint_from(place1: &Place, place2: &Place) -> bool {
    place1.is_disjoint_from(place2)
}

fn place_disjoint_from_or_prefix_of(place1: &Place, place2: &Place) -> bool {
    place1.is_disjoint_from(place2) || place1.is_prefix_of(place2)
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
            (parameter_permits_access(env, flow, field.ty, access.give_to_drop(), place) => (env, flow))
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

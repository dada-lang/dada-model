use formality_core::{judgment_fn, Cons};

use crate::{
    grammar::{Access, FieldDecl, Parameter, Place, Ty},
    type_system::{
        env::Env,
        liveness::LivePlaces,
        perms::{liens, Lien},
        places::place_fields,
        quantifiers::fold,
    },
};

judgment_fn! {
    /// Convenience rule for applying same access to multiple places.
    pub fn accesses_permitted(
        env: Env,
        live_after: LivePlaces,
        access: Access,
        places: Vec<Place>,
    ) => Env {
        debug(access, places, env, live_after)

        (
            (fold(env, places, &|env, place| {
                access_permitted(env, &live_after, &access, place)
            }) => env)
            -------------------------------- ("accesses_permitted")
            (accesses_permitted(env, live_after, access, places) => env)
        )
    }
}

judgment_fn! {
    /// True if `place` is initialized and
    /// accessing it in the fashion given by `access` is permitted
    /// by the other variables in the environment.
    pub fn access_permitted(
        env: Env,
        live_after: LivePlaces,
        access: Access,
        place: Place,
    ) => Env {
        debug(access, place, env, live_after)

        (
            (env_permits_access(env, live_after, access, place) => env)
            -------------------------------- ("access_permitted")
            (access_permitted(env, live_after, access, place) => env)
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
        live_after: LivePlaces,
        access: Access,
        place: Place,
    ) => Env {
        debug(access, place, env, live_after)

        (
            (let live_var_tys: Vec<Ty> = live_after.vars().iter().map(|var| env.var_ty(var).unwrap()).cloned().collect())
            (parameters_permit_access(env, live_var_tys, &access, &place) => env)
            (accessed_place_permits_access(env, &live_after, access, &place) => env)
            -------------------------------- ("env_permits_access")
            (env_permits_access(env, live_after, access, place) => env)
        )
    }
}

judgment_fn! {
    fn parameters_permit_access(
        env: Env,
        parameters: Vec<Parameter>,
        access: Access,
        place: Place,
    ) => Env {
        debug(parameters, access, place, env)

        (
            -------------------------------- ("nil")
            (parameters_permit_access(env, (), _access, _place) => env)
        )


        (
            (parameter_permits_access(env, parameter, access, &place) => env)
            (parameters_permit_access(env, &parameters, access, &place) => env)
            -------------------------------- ("cons")
            (parameters_permit_access(env, Cons(parameter, parameters), access, place) => env)
        )
    }
}

judgment_fn! {
    pub fn parameter_permits_access(
        env: Env,
        parameter: Parameter,
        access: Access,
        place: Place,
    ) => Env {
        debug(parameter, access, place, env)

        (
            (liens(&env, p) => liens_p)
            (fold(&env, liens_p, &|env, lien| {
                lien_permit_access(env, lien, access, &place)
            }) => env)
            -------------------------------- ("parameter")
            (parameter_permits_access(env, p, access, place) => env)
        )
    }
}

judgment_fn! {
    fn lien_permit_access(
        env: Env,
        lien: Lien,
        access: Access,
        accessed_place: Place,
    ) => Env {
        debug(lien, access, accessed_place, env)

        (
            (shared_place_permits_access(place, access, accessed_place) => ())
            -------------------------------- ("shared")
            (lien_permit_access(env, Lien::Shared(place), access, accessed_place) => &env)
        )

        (
            (leased_place_permits_access(place, access, accessed_place) => ())
            -------------------------------- ("leased")
            (lien_permit_access(env, Lien::Leased(place), access, accessed_place) => &env)
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
        live_after: LivePlaces,
        access: Access,
        place: Place,
    ) => Env {
        debug(place, access, env, live_after)

        (
            (if !live_after.is_live(&place.var))!
            --------------------------------- ("not live")
            (accessed_place_permits_access(env, live_after, _access, place) => env)
        )

        (
            (if live_after.is_live(&place.var))!
            (let place_prefixes = place.strict_prefixes())
            (fold(env, place_prefixes, &|env, place_prefix| {
                accessed_place_prefix_permits_access(env, place_prefix, access, &place)
            }) => env)
            --------------------------------- ("live")
            (accessed_place_permits_access(env, live_after, access, place) => env)
        )
    }
}

judgment_fn! {
    fn accessed_place_prefix_permits_access(
        env: Env,
        place_prefix: Place,
        access: Access,
        place: Place,
    ) => Env {
        debug(place_prefix, place, access, env)
        assert(place_prefix.is_strict_prefix_of(&place))

        (
            (place_fields(&env, &place_prefix) => fields)
            (fold(&env, fields, &|env, field| {
                field_of_accessed_place_prefix_permits_access(env, &place_prefix, field, access, &place)
            }) => env)
            --------------------------------- ("live")
            (accessed_place_prefix_permits_access(env, place_prefix, access, place) => env)
        )
    }
}

judgment_fn! {
    fn field_of_accessed_place_prefix_permits_access(
        env: Env,
        place_prefix: Place,
        field: FieldDecl,
        access: Access,
        place: Place,
    ) => Env {
        debug(place_prefix, field, place, access, env)
        assert(place_prefix.is_strict_prefix_of(&place))

        (
            (let place_with_field = place_prefix.project(&field.name))
            (if !place_with_field.is_prefix_of(&place))!

            // Subtle: treat GIVE as DROP here. This means that if the user is giving `foo.bar`,
            // then we don't allow a share of (say) `foo.bar.baz`. Ordinarily this would be ok
            // because we could track the new name, but when the share is coming from a field
            // inside the struct, we can't update those types as they live in the field declaration
            // and not the environment. So we treat GIVE as a DROP, which does not track new locations.
            (parameter_permits_access(env, field.ty, access.give_to_drop(), place) => env)
            --------------------------------- ("not accessed place")
            (field_of_accessed_place_prefix_permits_access(env, place_prefix, field, access, place) => env)
        )


        (
            (let place_with_field = place_prefix.project(&field.name))
            (if place_with_field.is_prefix_of(&place))!
            --------------------------------- ("is accessed place")
            (field_of_accessed_place_prefix_permits_access(env, place_prefix, field, _access, place) => env)
        )
    }
}

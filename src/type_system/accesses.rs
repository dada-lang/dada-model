use formality_core::{judgment_fn, Cons, Set};

use crate::{
    grammar::{Access, FieldDecl, NamedTy, Parameter, Perm, Place, Ty},
    type_system::{
        env::Env,
        flow::Flow,
        is_::is_unique,
        liens::{lien_chains, ty_chains, Lien, LienChain, My, TyChain},
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
    /// True if accessing `place` in the fashion given by `access`
    /// is permitted by the other variables in the environment.
    /// **Does not check if `place` is initialized.**
    /// This is because this judgment is used as part of assignments.
    pub fn can_mutate(
        env: Env,
        place: Place,
    ) => Env {
        debug(place, env)

        (
            (if let None = place.owner())!
            -------------------------------- ("mutate var")
            (can_mutate(env, place) => env)
        )

        (
            (if let Some(owner_place) = place.owner())!
            (place_ty(&env, owner_place) => owner_ty)
            (is_unique(&env, owner_ty) => env)
            -------------------------------- ("mutate place")
            (can_mutate(env, place) => env)
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
            (lien_set_from_parameter(env, p) => (env, lien_set))
            (fold((env, &flow), lien_set, &|(env, flow), lien| {
                lien_permit_access(env, flow, lien, access, &place)
            }) => (env, flow))
            -------------------------------- ("parameter")
            (parameter_permits_access(env, flow, p, access, place) => (env, flow))
        )
    }
}

judgment_fn! {
    fn lien_permit_access(
        env: Env,
        flow: Flow,
        lien: Lien,
        access: Access,
        accessed_place: Place,
    ) => (Env, Flow) {
        debug(lien, access, accessed_place, env, flow)

        (
            -------------------------------- ("our")
            (lien_permit_access(env, flow, Lien::Our, _access, _accessed_place) => (&env, &flow))
        )

        (
            (shared_place_permits_access(place, access, accessed_place) => ())
            -------------------------------- ("our")
            (lien_permit_access(env, flow, Lien::Shared(place), access, accessed_place) => (&env, &flow))
        )

        (
            (leased_place_permits_access(place, access, accessed_place) => ())
            -------------------------------- ("our")
            (lien_permit_access(env, flow, Lien::Leased(place), access, accessed_place) => (&env, &flow))
        )

        (
            -------------------------------- ("var")
            (lien_permit_access(env, flow, Lien::Var(_), _access, _accessed_place) => (&env, &flow))
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

judgment_fn! {
    fn lien_set_from_chain(
        env: Env,
        a: LienChain,
    ) => (Env, Set<Lien>) {
        debug(a, env)

        (
            ----------------------------------- ("my")
            (lien_set_from_chain(env, My()) => (env, ()))
        )

        (
            (lien_set_from_chain(env, &chain) => (env, lien_set0))
            ----------------------------------- ("our")
            (lien_set_from_chain(env, Cons(Lien::Our, chain)) => (env, Cons(Lien::Our, lien_set0)))
        )

        (
            (lien_set_from_place(env, &place) => (env, lien_set0))
            (lien_set_from_chain(env, &chain) => (env, lien_set1))
            ----------------------------------- ("sh")
            (lien_set_from_chain(env, Cons(Lien::Shared(place), chain)) => (env, Cons(Lien::shared(&place), (&lien_set0, lien_set1))))
        )

        (
            (lien_set_from_place(env, &place) => (env, lien_set0))
            (lien_set_from_chain(env, &chain) => (env, lien_set1))
            ----------------------------------- ("l")
            (lien_set_from_chain(env, Cons(Lien::Leased(place), chain)) => (env, Cons(Lien::leased(&place), (&lien_set0, lien_set1))))
        )


        (
            (lien_set_from_chain(env, chain) => (env, lien_set0))
            ----------------------------------- ("var")
            (lien_set_from_chain(env, Cons(Lien::Var(var), chain)) => (env, Cons(Lien::Var(var), lien_set0)))
        )
    }
}

judgment_fn! {
    fn lien_set_from_place(
        env: Env,
        a: Place,
    ) => (Env, Set<Lien>) {
        debug(a, env)

        (
            (place_ty(&env, &place) => ty)
            (lien_set_from_parameter(&env, ty) => (env, lien_set))
            ----------------------------------- ("nil")
            (lien_set_from_place(env, place) => (env, lien_set))
        )

    }
}

judgment_fn! {
    fn lien_set_from_parameter(
        env: Env,
        a: Parameter,
    ) => (Env, Set<Lien>) {
        debug(a, env)

        (
            (ty_chains(env, My(), ty) => (env, ty_chains))
            (lien_set_from_ty_chains(env, ty_chains) => (env, lien_set))
            ----------------------------------- ("nil")
            (lien_set_from_parameter(env, ty: Ty) => (env, lien_set))
        )

        (
            (lien_chains(env, My(), perm) => (env, chains))
            (lien_set_from_chains(env, chains) => (env, lien_set))
            ----------------------------------- ("nil")
            (lien_set_from_parameter(env, perm: Perm) => (env, lien_set))
        )
    }
}

judgment_fn! {
    fn lien_set_from_parameters(
        env: Env,
        a: Vec<Parameter>,
    ) => (Env, Set<Lien>) {
        debug(a, env)

        (
            ----------------------------------- ("nil")
            (lien_set_from_parameters(env, ()) => (env, ()))
        )


        (
            (lien_set_from_parameter(env, p) => (env, lien_set0))
            (lien_set_from_parameters(env, &ps) => (env, lien_set1))
            ----------------------------------- ("cons")
            (lien_set_from_parameters(env, Cons(p, ps)) => (env, (&lien_set0, lien_set1)))
        )
    }
}

judgment_fn! {
    fn lien_set_from_ty_chains(
        env: Env,
        a: Set<TyChain>,
    ) => (Env, Set<Lien>) {
        debug(a, env)

        (
            ----------------------------------- ("nil")
            (lien_set_from_ty_chains(env, ()) => (env, ()))
        )

        (
            (lien_set_from_chain(env, liens) => (env, lien_set0))
            (lien_set_from_ty_chains(env, &liens1) => (env, lien_set1))
            ----------------------------------- ("nil")
            (lien_set_from_ty_chains(env, Cons(TyChain::Var(liens, _), liens1)) => (env, (&lien_set0, lien_set1)))
        )

        (
            (lien_set_from_chain(env, liens) => (env, lien_set0))
            (lien_set_from_ty_chains(env, &liens1) => (env, lien_set1))
            (lien_set_from_parameters(env, &parameters) => (env, lien_set2))
            ----------------------------------- ("nil")
            (lien_set_from_ty_chains(env, Cons(TyChain::NamedTy(liens, NamedTy { name: _, parameters }), liens1)) => (env, (&lien_set0, &lien_set1, lien_set2)))
        )
    }
}

judgment_fn! {
    fn lien_set_from_chains(
        env: Env,
        a: Set<LienChain>,
    ) => (Env, Set<Lien>) {
        debug(a, env)

        (
            ----------------------------------- ("nil")
            (lien_set_from_chains(env, ()) => (env, ()))
        )

        (
            (lien_set_from_chain(env, liens0) => (env, lien_set0))
            (lien_set_from_chains(env, &liens1) => (env, lien_set1))
            ----------------------------------- ("nil")
            (lien_set_from_chains(env, Cons(liens0, liens1)) => (env, (&lien_set0, lien_set1)))
        )
    }
}

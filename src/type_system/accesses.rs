use formality_core::{judgment_fn, Cons, Set};

use crate::{
    dada_lang::grammar::Variable,
    grammar::{Access, LocalVariableDecl, NamedTy, Parameter, Perm, Place, Ty, Var},
    type_system::{env::Env, flow::Flow, liveness::LiveVars, places::place_ty},
};

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

        // FIXME: This isn't exactly right for Access::Give -- *giving* a place can be
        // allowed even when borrowed, it rewrites the types of other things that may reference
        // this place.

        (
            (live_variables_permit_access(&env, flow, &live_after, live_after.vars(), access, place) => (env, flow))
            -------------------------------- ("env_permits_access")
            (env_permits_access(env, flow, live_after, access, place) => (env, flow))
        )
    }
}

judgment_fn! {
    fn live_variables_permit_access(
        env: Env,
        flow: Flow,
        live_after: LiveVars,
        variables: Set<Var>,
        access: Access,
        place: Place,
    ) => (Env, Flow) {
        debug(variables, access, place, env, flow, live_after)

        (
            -------------------------------- ("nil")
            (live_variables_permit_access(env, flow, _live_after, (), _access, _place) => (env, flow))
        )

        (
            (assert live_after.is_live(&var))
            (let ty = env.var_ty(&var).unwrap().clone())
            (ty_permits_access(env, flow, ty, access, &place) => (env, flow))
            (live_variables_permit_access(env, flow, &live_after, &vars, access, &place) => (env, flow))
            -------------------------------- ("cons, initialized variable")
            (live_variables_permit_access(env, flow, live_after, Cons(var, vars), access, place) => (env, flow))
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
            -------------------------------- ("ty")
            (parameter_permits_access(env, flow, Parameter::Perm(perm), access, place) => (env, flow))
        )
    }
}

judgment_fn! {
    fn ty_permits_access(
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
            (perm_permits_access(env, flow, Perm::Shared(perm_places) | Perm::Leased(perm_places) | Perm::Given(perm_places) | Perm::ShLeased(perm_places), access, accessed_place) => (env, flow))
        )

        // If this is a shared access, and the borrow was a shared borrow, that's fine.
        (
            (perm_places_permit_access(env, flow, perm_places, Access::Share, accessed_place) => (env, flow))
            -------------------------------- ("shared-shared")
            (perm_permits_access(env, flow, Perm::Shared(perm_places) | Perm::ShLeased(perm_places), Access::Share, accessed_place) => (env, flow))
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
    }
}
/// True if every place listed in `places` is "covered" by one of the places in
/// `covering_places`. A place P1 *covers* a place P2 if it is a prefix:
/// for example, `x.y` covers `x.y` and `x.y.z` but not `x.z` or `x1`.
fn place_disjoint_from_all_of(accessed_place: &Place, perm_places: &Set<Place>) -> bool {
    perm_places
        .iter()
        .all(|place| place.is_disjoint_from(accessed_place))
}

use formality_core::{judgment_fn, Cons, Set};

use crate::{
    dada_lang::grammar::Variable,
    grammar::{Access, LocalVariableDecl, NamedTy, Parameter, Perm, Place, Ty},
    type_system::{env::Env, flow::Flow, type_places::place_ty, type_subtype::is_shared},
};

judgment_fn! {
    pub fn access_permitted(
        env: Env,
        flow: Flow,
        access: Access,
        place: Place,
    ) => (Env, Flow) {
        debug(access, place, env, flow)

        // FIXME: This isn't exactly right for Access::Give -- *giving* a place can be
        // allowed even when borrowed, it rewrites the types of other things that may reference
        // this place.

        (
            (let local_variables = env.local_variables())
            (variables_permit_access(&env, flow, local_variables, access, place) => (env, flow))
            -------------------------------- ("nil")
            (access_permitted(env, flow, access, place) => (env, flow))
        )
    }
}

judgment_fn! {
    pub fn variables_permit_access(
        env: Env,
        flow: Flow,
        variables: Vec<LocalVariableDecl>,
        access: Access,
        place: Place,
    ) => (Env, Flow) {
        debug(variables, access, place, env, flow)

        (
            -------------------------------- ("nil")
            (variables_permit_access(env, flow, (), _access, _place) => (env, flow))
        )

        (
            (let LocalVariableDecl { name: _, ty } = variable)
            // FIXME: take flow into account; variables (or parts of variables) may be cleared
            (ty_permits_access(env, flow, ty, access, &place) => (env, flow))
            (variables_permit_access(env, flow, &variables, access, &place) => (env, flow))
            -------------------------------- ("cons")
            (variables_permit_access(env, flow, Cons(variable, variables), access, place) => (env, flow))
        )
    }
}

judgment_fn! {
    pub fn parameters_permit_access(
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
    pub fn perm_permits_access(
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

        (
            (if place_disjoint_from_all_of(&accessed_place, &perm_places))
            -------------------------------- ("disjoint")
            (perm_permits_access(env, flow, Perm::Shared(perm_places) | Perm::Leased(perm_places) | Perm::Given(perm_places) | Perm::ShLeased(perm_places), _access, accessed_place) => (env, flow))
        )

        // If a place `P` has a value of shared type,
        // then trying to access `P` cannot cause an error.
        // Even if there are `given(P)` or `leased(P)` permissions out there,
        // they could only at most share the object referred to by `P`.
        (
            (place_ty(&env, place) => place_ty)
            (is_shared(&env, place_ty) => env)
            -------------------------------- ("shared-shared")
            (perm_permits_access(env, flow, _perm, _access, place) => (env, &flow))
        )

        (
            // FIXME: check the variables visible by `v` and allow access only if place is not one of those
            -------------------------------- ("universal")
            (perm_permits_access(env, flow, Variable::UniversalVar(_), _access, _place) => (env, flow))
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

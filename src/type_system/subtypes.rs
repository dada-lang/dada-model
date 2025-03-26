use formality_core::{judgment_fn, Cons};

use crate::{
    grammar::{NamedTy, Parameter, Perm, Place, VarianceKind},
    type_system::{
        env::Env,
        liveness::LivePlaces,
        predicates::{prove_is_copy, prove_is_lent, prove_is_move, prove_is_owned},
        quantifiers::for_all,
        red_terms::{red_term, red_term_under, RedTerm, RedTy},
    },
};

use super::red_terms::RedPerm;

judgment_fn! {
    /// Provable if `a <: b` in an owned (`my`) context.
    pub fn sub(
        env: Env,
        live_after: LivePlaces,
        a: Parameter,
        b: Parameter,
    ) => () {
        debug(a, b, live_after, env)

        (
            (sub_under(env, live_after, Perm::My, a, Perm::My, b) => ())
            ------------------------------- ("sub")
            (sub(env, live_after, a, b) => ())
        )
    }
}

judgment_fn! {
    /// Provable if `a <: b` in an owned (`my`) context.
    fn sub_under(
        env: Env,
        live_after: LivePlaces,
        perm_a: Perm,
        a: Parameter,
        perm_b: Perm,
        b: Parameter,
    ) => () {
        debug(perm_a, a, perm_b, b, live_after, env)

        (
            (red_term_under(&env, &perm_a, &a) => red_term_a)
            (red_term_under(&env, &perm_b, &b) => red_term_b)
            (sub_red_terms(&env, &live_after, &red_term_a, &red_term_b) => ())
            ------------------------------- ("sub")
            (sub_under(env, live_after, perm_a0, a, perm_b0, b) => ())
        )
    }
}

judgment_fn! {
    /// Provable if `a <: b` in an owned (`my`) context.
    fn sub_red_terms(
        env: Env,
        live_after: LivePlaces,
        red_term_a: RedTerm,
        red_term_b: RedTerm,
    ) => () {
        debug(red_term_a, red_term_b, live_after, env)

        (
            (if let RedTy::Var(var_a) = a.red_ty)
            (if let RedTy::Var(var_b) = b.red_ty)
            (if var_a == var_b)!
            (sub_red_perms(env, live_after, &a.red_perm, &b.red_perm) => ())
            ------------------------------- ("sub-vars-eq")
            (sub_red_terms(env, live_after, a, b) => ())
        )

        (
            (if let RedTy::NamedTy(NamedTy { name: name_a, parameters: parameters_a }) = a.red_ty)
            (if let RedTy::NamedTy(NamedTy { name: name_b, parameters: parameters_b }) = b.red_ty)
            (if name_a == name_b)!
            (sub_red_perms(&env, &live_after, &a.red_perm, &b.red_perm) => ())
            (let variances = env.variances(&name_a)?)
            (if parameters_a.len() == variances.len())
            (if parameters_b.len() == variances.len())
            (for_all(0..variances.len(), &|&i| {
                sub_generic_parameter(&env, &live_after, &variances[i], &a.red_perm, &parameters_a[i], &b.red_perm, &parameters_b[i])
            }) => ())
            ------------------------------- ("sub-classes")
            (sub_red_terms(env, live_after, a, b) => ())
        )

        (
            (if let RedTy::None = a.red_ty)
            (if let RedTy::None = b.red_ty)!
            (sub_red_perms(env, live_after, &a.red_perm, &b.red_perm) => ())
            ------------------------------- ("sub-none")
            (sub_red_terms(env, live_after, a, b) => ())
        )
    }
}

judgment_fn! {
    fn sub_red_perms(
        env: Env,
        live_after: LivePlaces,
        a: RedPerm,
        b: RedPerm,
    ) => () {
        debug(a, b, live_after, env)

        (
            (prove_is_move(&env, &perm_a) => ())
            (prove_is_move(&env, &perm_a) => ())
            (prove_is_owned(&env, &perm_b) => ())
            ------------------------------- ("my-sub-owned")
            (sub_red_perms(env, _live_after, perm_a, perm_b) => ())
        )

        (
            (prove_is_owned(&env, &perm_a) => ())
            (prove_is_move(&env, &perm_a) => ())
            (prove_is_copy(&env, &perm_b) => ())
            ------------------------------- ("my-sub-copy")
            (sub_red_perms(env, _live_after, perm_a, perm_b) => ())
        )

        (
            (prove_is_owned(&env, &perm_a) => ())
            (prove_is_copy(&env, &perm_a) => ())
            (prove_is_copy(&env, &perm_b) => ())
            ------------------------------- ("our-sub-copy")
            (sub_red_perms(env, _live_after, perm_a, perm_b) => ())
        )

        (
            (let chain_a: RedPerm = chain_a)
            (let chain_b: RedPerm = chain_b)
            (if places_a.iter().all(|place_a| {
                places_b.iter().any(|place_b| {
                    place_b.is_prefix_of(&place_a)
                })
            }))
            (sub_red_perms(env, live_after, chain_a, chain_b) => ())
            ------------------------------- ("given-vs-given")
            (sub_red_perms(env, live_after, Cons(Perm::Given(places_a), chain_a), Cons(Perm::Given(places_b), chain_b)) => ())
        )

        (
            (let chain_a: RedPerm = chain_a)
            (let chain_b: RedPerm = chain_b)
            (if places_a.iter().all(|place_a| {
                places_b.iter().any(|place_b| {
                    place_b.is_prefix_of(&place_a)
                })
            }))
            (sub_red_perms(env, live_after, chain_a, chain_b) => ())
            ------------------------------- ("shared-vs-shared")
            (sub_red_perms(env, live_after, Cons(Perm::Shared(places_a), chain_a), Cons(Perm::Shared(places_b), chain_b)) => ())
        )

        (
            (let chain_a: RedPerm = chain_a)
            (let chain_b: RedPerm = chain_b)
            (if places_a.iter().all(|place_a| {
                places_b.iter().any(|place_b| {
                    place_b.is_prefix_of(&place_a)
                })
            }))
            (sub_red_perms(env, live_after, chain_a, chain_b) => ())
            ------------------------------- ("shared-vs-our-leased")
            (sub_red_perms(env, live_after, Cons(Perm::Shared(places_a), chain_a), Cons(Perm::Our, Cons(Perm::Leased(places_b), chain_b))) => ())
        )

        (
            (let chain_a: RedPerm = chain_a)
            (let chain_b: RedPerm = chain_b)
            (if places_a.iter().all(|place_a| {
                places_b.iter().any(|place_b| {
                    place_b.is_prefix_of(&place_a)
                })
            }))
            (sub_red_perms(env, live_after, chain_a, chain_b) => ())
            ------------------------------- ("leased-vs-leased")
            (sub_red_perms(env, live_after, Cons(Perm::Leased(places_a), chain_a), Cons(Perm::Leased(places_b), chain_b)) => ())
        )

        (
            (let chain_a: RedPerm = chain_a)
            (let chain_b: RedPerm = chain_b)
            (sub_red_perms(env, live_after, chain_a, chain_b) => ())
            ------------------------------- ("our-vs-our")
            (sub_red_perms(env, live_after, Cons(Perm::Our, chain_a), Cons(Perm::Our, chain_b)) => ())
        )

        (
            (let chain_a: RedPerm = chain_a)
            (let chain_b: RedPerm = chain_b)
            (if var_a == var_b)!
            (sub_red_perms(env, live_after, chain_a, chain_b) => ())
            ------------------------------- ("var-vs-var")
            (sub_red_perms(env, live_after, Cons(Perm::Var(var_a), chain_a), Cons(Perm::Var(var_b), chain_b)) => ())
        )

        (
            (let perm_a: RedPerm = perm_a)
            (for_all(&places_a, &|&place_a| {
                sub_dead_given(&env, &live_after, place_a, &perm_a, &perm_b)
            }) => ())
            ------------------------------- ("given-dead")
            (sub_red_perms(env, live_after, Cons(Perm::Given(places_a), perm_a), perm_b) => ())
        )

        (
            (let perm_a: RedPerm = perm_a)
            (for_all(&places_a, &|&place_a| {
                sub_dead_leased(&env, &live_after, place_a, &perm_a, &perm_b)
            }) => ())
            ------------------------------- ("leased-dead")
            (sub_red_perms(env, live_after, Cons(Perm::Leased(places_a), perm_a), perm_b) => ())
        )

        (
            (let perm_a: RedPerm = perm_a)
            (for_all(&places_a, &|&place_a| {
                sub_dead_shared(&env, &live_after, place_a, &perm_a, &perm_b)
            }) => ())
            ------------------------------- ("shared-dead")
            (sub_red_perms(env, live_after, Cons(Perm::Shared(places_a), perm_a), perm_b) => ())
        )
    }
}

judgment_fn! {
    fn sub_dead_given(
        env: Env,
        live_after: LivePlaces,
        place_a: Place,
        perm_a: RedPerm,
        b: RedPerm,
    ) => () {
        debug(place_a, perm_a, b, live_after, env)

        (
            (if !live_after.is_live(&place_a))!
            (let ty_a = env.place_ty(&place_a)?)
            (red_term(&env, &ty_a) => red_term_a)
            (sub_under(&env, &live_after, &red_term_a.red_perm, &perm_a, Perm::My, &perm_b) => ())
            ------------------------------- ("sub_dead_leased")
            (sub_dead_given(env, live_after, place_a, perm_a, perm_b) => ())
        )
    }
}

judgment_fn! {
    fn sub_dead_leased(
        env: Env,
        live_after: LivePlaces,
        place_a: Place,
        perm_a: RedPerm,
        b: RedPerm,
    ) => () {
        debug(place_a, perm_a, b, live_after, env)

        (
            (if !live_after.is_live(&place_a))!
            (let ty_a = env.place_ty(&place_a)?)
            (prove_is_lent(&env, &ty_a) => ())
            (red_term(&env, &ty_a) => red_term_a)
            (sub_under(&env, &live_after, &red_term_a.red_perm, &perm_a, Perm::My, &perm_b) => ())
            ------------------------------- ("sub_dead_leased")
            (sub_dead_leased(env, live_after, place_a, perm_a, perm_b) => ())
        )
    }
}

judgment_fn! {
    fn sub_dead_shared(
        env: Env,
        live_after: LivePlaces,
        place_a: Place,
        perm_a: RedPerm,
        b: RedPerm,
    ) => () {
        debug(place_a, perm_a, b, live_after, env)

        (
            (if !live_after.is_live(&place_a))!
            (let ty_a = env.place_ty(&place_a)?)
            (prove_is_lent(&env, &ty_a) => ())
            (red_term(&env, &ty_a) => red_term_a)
            (sub_under(&env, &live_after, Perm::apply(Perm::Our, red_term_a.red_perm), &perm_a, Perm::My, &perm_b) => ())
            ------------------------------- ("sub_dead_shared")
            (sub_dead_shared(env, live_after, place_a, perm_a, perm_b) => ())
        )
    }
}

judgment_fn! {
    fn sub_generic_parameter(
        env: Env,
        live_after: LivePlaces,
        variances: Vec<VarianceKind>,
        perm_a: Perm,
        a: Parameter,
        perm_b: Perm,
        b: Parameter,
    ) => () {
        debug(variances, a, b, perm_a, perm_b, live_after, env)

        // invariant is always ok

        (
            (sub(&env, &live_after, &a, &b) => ())
            (sub(&env, &live_after, &b, &a) => ())
            ------------------------------- ("invariant")
            (sub_generic_parameter(env, live_after, _v, _perm_a, a, _perm_b, b) => ())
        )

        // We want to allow covariant unless the values are leased.
        // We do that by allowing it if the target type is `copy` or `my`.
        //
        // Here we rule out any form of variance (relative, atomic) and
        // limit that to invariant. This is stricter than needed.

        (
            (prove_is_copy(&env, &perm_b) => ())
            (sub_under(&env, &live_after, &perm_a, &a, &perm_b, &b) => ())
            ------------------------------- ("covariant-copy")
            (sub_generic_parameter(env, live_after, (), perm_a, a, perm_b, b) => ())
        )

        (
            (prove_is_owned(&env, &perm_b) => ())
            (sub_under(&env, &live_after, &perm_a, &a, &perm_b, &b) => ())
            ------------------------------- ("covariant-owned")
            (sub_generic_parameter(env, live_after, (), perm_a, a, perm_b, b) => ())
        )
    }
}

fn implies(a: bool, b: bool) -> bool {
    !a || (a && b)
}

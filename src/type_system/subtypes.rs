use formality_core::{judgment_fn, ProvenSet};

use crate::{
    grammar::{ty_impls::PermTy, NamedTy, Parameter, Perm, Ty, VarianceKind},
    type_system::{
        env::Env,
        liveness::LivePlaces,
        predicates::{prove_is_owned, prove_is_shared},
        quantifiers::for_all,
        redperms::sub_red_perms,
        subperms::sub_perms,
    },
};

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
            // These two ought to be equivalent
            (sub_perms_both_ways(&env, &live_after, &perm_a, &perm_b) => ())
            ------------------------------- ("sub-perms")
            (sub(env, live_after, perm_a: Perm, perm_b: Perm) => ())
        )

        (
            (if var_a == var_b)!
            (sub_perms_both_ways(env, live_after, perm_a, perm_b) => ())
            ------------------------------- ("sub-eq-vars")
            (sub(env, live_after, PermTy(perm_a, Ty::Var(var_a)), PermTy(perm_b, Ty::Var(var_b))) => ())
        )

        (
            (if let Ty::NamedTy(NamedTy { name: name_a, parameters: parameters_a }) = ty_a)
            (if let Ty::NamedTy(NamedTy { name: name_b, parameters: parameters_b }) = ty_b)
            (if name_a == name_b)!
            (sub_perms_both_ways(&env, &live_after, &perm_a, &perm_b) => ())
            (let variances = env.variances(&name_a)?)
            (if parameters_a.len() == variances.len())
            (if parameters_b.len() == variances.len())
            (for_all(0..variances.len(), &|&i| {
                sub_generic_parameter(&env, &live_after, &variances[i], &perm_a, &parameters_a[i], &perm_b, &parameters_b[i])
            }) => ())
            ------------------------------- ("sub-classes")
            (sub(env, live_after, PermTy(perm_a, ty_a), PermTy(perm_b, ty_b)) => ())
        )
    }
}

judgment_fn! {
    fn sub_perms_both_ways(
        env: Env,
        live_after: LivePlaces,
        a: Perm,
        b: Perm,
    ) => () {
        debug(a, b, live_after, env)

        (
            // These two ought to be equivalent
            (both_provable(
                sub_perms(&env, &live_after, &perm_a, &perm_b),
                sub_red_perms(&env, &live_after, &perm_a, &perm_b),
            ) => ())
            // (sub_red_perms(&env, &live_after, &perm_a, &perm_b) => ())
            ------------------------------- ("sub-perms")
            (sub_perms_both_ways(env, live_after, perm_a, perm_b) => ())
        )
    }
}

fn both_provable(set_a: ProvenSet<()>, set_b: ProvenSet<()>) -> ProvenSet<()> {
    eprintln!("both_provable: {set_a:?} and {set_b:?}");
    match (set_a.into_set(), set_b.into_set()) {
        (Ok(_), Ok(_)) => ProvenSet::singleton(()),
        (Err(err_a), Err(_)) => ProvenSet::from(*err_a),
        (Ok(_), Err(err)) | (Err(err), Ok(_)) => {
            panic!("one set of rules is provable and the other is not: {err}")
        }
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
        debug(perm_a, a, perm_b, b, variances, live_after, env)

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
            (prove_is_shared(&env, &perm_b) => ())
            (sub(&env, &live_after, perm_a.apply_to_parameter(&a), perm_b.apply_to_parameter(&b)) => ())
            ------------------------------- ("covariant-copy")
            (sub_generic_parameter(env, live_after, (), perm_a, a, perm_b, b) => ())
        )

        (
            (prove_is_owned(&env, &perm_b) => ())
            (sub(&env, &live_after, perm_a.apply_to_parameter(&a), perm_b.apply_to_parameter(&b)) => ())
            ------------------------------- ("covariant-owned")
            (sub_generic_parameter(env, live_after, (), perm_a, a, perm_b, b) => ())
        )
    }
}

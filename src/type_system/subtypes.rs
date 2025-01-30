use formality_core::{judgment_fn, Set};

use crate::{
    grammar::{IsCopy, IsOwned, NamedTy, Parameter, VarianceKind},
    type_system::{
        env::Env,
        lien2::{lien_datas, lien_set_is_copy, lien_set_is_owned, Data, Lien, LienData},
        liveness::LivePlaces,
        quantifiers::for_all,
    },
};

use super::lien2::LienSet;

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
            (sub_under(env, live_after, (), a, (), b) => ())
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
        cx_a: LienSet,
        a: Parameter,
        cx_b: LienSet,
        b: Parameter,
    ) => () {
        debug(cx_a, a, cx_b, b, live_after, env)

        (
            (lien_datas(&env, cx_a, a) => lien_datas_a)
            (lien_datas(&env, &cx_b, &b) => lien_datas_b)
            (for_all(&lien_datas_a, &|lien_data_a| sub_some(&env, &live_after, lien_data_a, &lien_datas_b)) => ())
            ------------------------------- ("sub")
            (sub_under(env, live_after, cx_a, a, cx_b, b) => ())
        )
    }
}

judgment_fn! {
    fn sub_some(
        env: Env,
        live_after: LivePlaces,
        lien_data_a: LienData,
        lien_datas_b: Set<LienData>,
    ) => () {
        debug(lien_data_a, lien_datas_b, live_after, env)

        (
            (&lien_datas_b => lien_data_b)
            (sub_lien_data(&env, &live_after, &lien_data_a, &lien_data_b) => ())
            ------------------------------- ("sub-some")
            (sub_some(env, live_after, lien_data_a, lien_datas_b) => ())
        )
    }
}

judgment_fn! {
    fn sub_lien_data(
        env: Env,
        live_after: LivePlaces,
        lien_data_a: LienData,
        lien_data_b: LienData,
    ) => () {
        debug(lien_data_a, lien_data_b, live_after, env)

        (
            (if let LienData { liens: liens_a, data: Data::Var(var_a) } = lien_data_a)
            (if let LienData { liens: liens_b, data: Data::Var(var_b) } = lien_data_b)
            (if var_a == var_b)!
            (sub_lien_sets(env, live_after, liens_a, liens_b) => ())
            ------------------------------- ("sub-vars-eq")
            (sub_lien_data(env, live_after, lien_data_a, lien_data_b) => ())
        )

        (
            (if let LienData { liens: liens_a, data: Data::NamedTy(NamedTy { name: name_a, parameters: parameters_a }) } = lien_data_a)
            (if let LienData { liens: liens_b, data: Data::NamedTy(NamedTy { name: name_b, parameters: parameters_b }) } = lien_data_b)
            (if name_a == name_b)!
            (sub_lien_sets(&env, &live_after, &liens_a, &liens_b) => ())
            (let variances = env.variances(&name_a)?)
            (if parameters_a.len() == variances.len())
            (if parameters_b.len() == variances.len())
            (for_all(0..variances.len(), &|&i| {
                sub_generic_parameter(&env, &live_after, &variances[i], &liens_a, &parameters_a[i], &liens_b, &parameters_b[i])
            }) => ())
            ------------------------------- ("sub-named")
            (sub_lien_data(env, live_after, lien_data_a, lien_data_b) => ())
        )

        (
            (if let LienData { liens: liens_a, data: Data::None } = lien_data_a)
            (if let LienData { liens: liens_b, data: Data::None } = lien_data_b)!
            (sub_lien_sets(env, live_after, liens_a, liens_b) => ())
            ------------------------------- ("sub-no-data")
            (sub_lien_data(env, live_after, lien_data_a, lien_data_b) => ())
        )
    }
}

judgment_fn! {
    fn sub_lien_sets(
        env: Env,
        live_after: LivePlaces,
        liens_a: LienSet,
        liens_b: LienSet,
    ) => () {
        debug(liens_a, liens_b, live_after, env)

        (
            (for_all(&liens_a, &|lien_a| sub_some_lien(&env, &live_after, &lien_a, &liens_b)) => ())
            ------------------------------- ("sub-some")
            (sub_lien_sets(env, live_after, liens_a, liens_b) => ())
        )
    }
}

judgment_fn! {
    fn layout_compatible(
        env: Env,
        liens_a: LienSet,
        liens_b: LienSet,
    ) => () {
        debug(liens_a, liens_b, env)

        (
            ------------------------------- ("FIXME")
            (layout_compatible(env, liens_a, liens_b) => ())
        )
    }
}

judgment_fn! {
    fn lien_set_is_copy_or_owned(
        env: Env,
        liens: LienSet,
    ) => () {
        debug(liens, env)

        (
            (lien_set_is_copy(env, liens) => ())
            ------------------------------- ("copy")
            (lien_set_is_copy_or_owned(env, liens) => ())
        )

        (
            (lien_set_is_owned(env, liens) => ())
            ------------------------------- ("owned")
            (lien_set_is_copy_or_owned(env, liens) => ())
        )
    }
}

judgment_fn! {
    fn sub_some_lien(
        env: Env,
        live_after: LivePlaces,
        lien_a: Lien,
        liens_b: LienSet,
    ) => () {
        debug(lien_a, liens_b, live_after, env)

        (
            (&liens_b => lien_b)
            (sub_lien(&env, &live_after, &lien_a, &lien_b) => ())
            ------------------------------- ("sub-some")
            (sub_some_lien(env, live_after, lien_a, liens_b) => ())
        )
    }
}

judgment_fn! {
    fn sub_lien(
        env: Env,
        live_after: LivePlaces,
        lien_a: Lien,
        lien_b: Lien,
    ) => () {
        debug(lien_a, lien_b, live_after, env)
        trivial(lien_a == lien_b => ())

        (
            (if b.is_prefix_of(&a))!
            ------------------------------- ("Leased-vs-Leased")
            (sub_lien(_env, _live_after, Lien::Leased(a), Lien::Leased(b)) => ())
        )

        (
            (if b.is_prefix_of(&a))!
            ------------------------------- ("Shared-vs-Shared")
            (sub_lien(_env, _live_after, Lien::Shared(a), Lien::Shared(b)) => ())
        )

        (
            (if env.is(&a, IsOwned))
            (if env.is(&b, IsCopy))
            ------------------------------- ("OwnedVar-vs-CopyVar")
            (sub_lien(env, _live_after, Lien::Var(a), Lien::Var(b)) => ())
        )

        (
            (if env.is(&v, IsOwned))
            ------------------------------- ("OwnedVar-vs-Copy")
            (sub_lien(env, _live_after, Lien::Var(v), Lien::Copy) => ())
        )

        (
            (if env.is(&v, IsCopy))
            ------------------------------- ("Copy-vs-CopyVar")
            (sub_lien(env, _live_after, Lien::Copy, Lien::Var(v)) => ())
        )
    }
}

judgment_fn! {
    fn sub_generic_parameter(
        env: Env,
        live_after: LivePlaces,
        variances: Vec<VarianceKind>,
        liens_a: LienSet,
        a: Parameter,
        liens_b: LienSet,
        b: Parameter,
    ) => () {
        debug(variances, a, b, liens_a, liens_b, live_after, env)

        // invariant is always ok

        (
            (sub(&env, &live_after, &a, &b) => ())
            (sub(&env, &live_after, &b, &a) => ())
            ------------------------------- ("invariant")
            (sub_generic_parameter(env, live_after, _v, _liens_a, a, _liens_b, b) => ())
        )

        // We want to allow covariant unless the values are leased.
        // We do that by allowing it if the target type is `copy` or `my`.
        //
        // Here we rule out any form of variance (relative, atomic) and
        // limit that to invariant. This is stricter than needed.


        (
            (lien_set_is_copy(&env, &liens_b) => ())
            (sub_under(&env, &live_after, &liens_a, &a, &liens_b, &b) => ())
            ------------------------------- ("covariant-copy")
            (sub_generic_parameter(env, live_after, (), liens_a, a, liens_b, b) => ())
        )


        (
            (lien_set_is_owned(&env, &liens_b) => ())
            (sub_under(&env, &live_after, &liens_a, &a, &liens_b, &b) => ())
            ------------------------------- ("covariant-owned")
            (sub_generic_parameter(env, live_after, (), liens_a, a, liens_b, b) => ())
        )
    }
}

judgment_fn! {
    fn dead_lien(
        env: Env,
        live_after: LivePlaces,
        a: Lien,
    ) => () {
        debug(a, live_after, env)
    }
}

use formality_core::{judgment_fn, Set};

use crate::{
    grammar::{IsMoved, IsOwned, NamedTy, Parameter, Place, UniversalVar, VarianceKind},
    type_system::{
        env::Env,
        liveness::LivePlaces,
        red_terms::{red_perms, red_terms, RedPerms, RedTerm, RedTy},
        places::place_ty,
        quantifiers::for_all,
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
            (sub_under_perms(env, live_after, RedPerms::my(), a, RedPerms::my(), b) => ())
            ------------------------------- ("sub")
            (sub(env, live_after, a, b) => ())
        )
    }
}

judgment_fn! {
    /// Provable if `a <: b` in an owned (`my`) context.
    fn sub_under_perms(
        env: Env,
        live_after: LivePlaces,
        perms_a: RedPerms,
        a: Parameter,
        perms_b: RedPerms,
        b: Parameter,
    ) => () {
        debug(perms_a, a, perms_b, b, live_after, env)

        (
            (red_terms(&env, &perms_a, &a) => lien_datas_a)
            (red_terms(&env, &perms_b, &b) => lien_datas_b)
            (for_all(&lien_datas_a, &|lien_data_a| sub_some(&env, &live_after, lien_data_a, &lien_datas_b)) => ())
            ------------------------------- ("sub")
            (sub_under_perms(env, live_after, perms_a, a, perms_b, b) => ())
        )
    }
}

judgment_fn! {
    fn sub_some(
        env: Env,
        live_after: LivePlaces,
        lien_data_a: RedTerm,
        lien_datas_b: Set<RedTerm>,
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
        lien_data_a: RedTerm,
        lien_data_b: RedTerm,
    ) => () {
        debug(lien_data_a, lien_data_b, live_after, env)

        (
            (if let RedTerm { perms: perms_a, ty: RedTy::Var(var_a) } = lien_data_a)
            (if let RedTerm { perms: perms_b, ty: RedTy::Var(var_b) } = lien_data_b)
            (if var_a == var_b)!
            (sub_perms(env, live_after, perms_a, perms_b) => ())
            ------------------------------- ("sub-vars-eq")
            (sub_lien_data(env, live_after, lien_data_a, lien_data_b) => ())
        )

        (
            (if let RedTerm { perms: perms_a, ty: RedTy::NamedTy(NamedTy { name: name_a, parameters: parameters_a }) } = lien_data_a)
            (if let RedTerm { perms: perms_b, ty: RedTy::NamedTy(NamedTy { name: name_b, parameters: parameters_b }) } = lien_data_b)
            (if name_a == name_b)!
            (sub_perms(&env, &live_after, &perms_a, &perms_b) => ())
            (let variances = env.variances(&name_a)?)
            (if parameters_a.len() == variances.len())
            (if parameters_b.len() == variances.len())
            (for_all(0..variances.len(), &|&i| {
                sub_generic_parameter(&env, &live_after, &variances[i], &perms_a, &parameters_a[i], &perms_b, &parameters_b[i])
            }) => ())
            ------------------------------- ("sub-named")
            (sub_lien_data(env, live_after, lien_data_a, lien_data_b) => ())
        )

        (
            (if let RedTerm { perms: perms_a, ty: RedTy::None } = lien_data_a)
            (if let RedTerm { perms: perms_b, ty: RedTy::None } = lien_data_b)!
            (sub_perms(env, live_after, perms_a, perms_b) => ())
            ------------------------------- ("sub-no-data")
            (sub_lien_data(env, live_after, lien_data_a, lien_data_b) => ())
        )
    }
}

judgment_fn! {
    fn sub_perms(
        env: Env,
        live_after: LivePlaces,
        perms_a: RedPerms,
        perms_b: RedPerms,
    ) => () {
        debug(perms_a, perms_b, live_after, env)

        (
            (if perms_a.is_copy(&env).implies(perms_b.is_copy(&env)))
            (if perms_a.is_lent(&env).implies(perms_b.is_lent(&env)))
            (if perms_a.layout(&env) == perms_b.layout(&env))

            (for_all(&perms_a.shared_from, &|place| covered(&env, &live_after, &place, &perms_b.shared_from)) => ())
            (for_all(&perms_a.leased_from, &|place| covered(&env, &live_after, &place, &perms_b.leased_from)) => ())
            (for_all(&perms_a.variables, &|variable| var_covered(&env, &variable, &perms_b.variables)) => ())
            ------------------------------- ("sub-some")
            (sub_perms(env, live_after, perms_a, perms_b) => ())
        )
    }
}

judgment_fn! {
    fn covered(
        env: Env,
        live_after: LivePlaces,
        place_a: Place,
        places_b: Set<Place>,
    ) => () {
        debug(place_a, places_b, live_after, env)

        (
            (if places_b.iter().any(|place_b| place_b.is_prefix_of(&place_a)))
            ------------------------------- ("prefix")
            (covered(_env, _live_after, place_a, places_b) => ())
        )

        (
            (if !live_after.is_live(&place))!
            (place_ty(&env, &place) => ty_place)
            (red_perms(&env, ty_place) => perms_place)
            (if perms_place.is_lent(&env))
            ------------------------------- ("dead")
            (covered(env, live_after, place, _places_b) => ())
        )
    }
}

judgment_fn! {
    fn var_covered(
        env: Env,
        var_a: UniversalVar,
        vars_b: Set<UniversalVar>,
    ) => () {
        debug(var_a, vars_b, env)

        (
            (if env.is(&var_a, IsOwned))
            (if env.is(&var_a, IsMoved))
            ------------------------------- ("my")
            (var_covered(_env, var_a, _vars_b) => ())
        )

        (
            (if vars_b.contains(&var_a))
            ------------------------------- ("contained")
            (var_covered(_env, var_a, vars_b) => ())
        )
    }
}

judgment_fn! {
    fn sub_generic_parameter(
        env: Env,
        live_after: LivePlaces,
        variances: Vec<VarianceKind>,
        liens_a: RedPerms,
        a: Parameter,
        liens_b: RedPerms,
        b: Parameter,
    ) => () {
        debug(variances, a, b, liens_a, liens_b, live_after, env)

        // invariant is always ok

        (
            (sub(&env, &live_after, &a, &b) => ())
            (sub(&env, &live_after, &b, &a) => ())
            ------------------------------- ("invariant")
            (sub_generic_parameter(env, live_after, _v, _perms_a, a, _perms_b, b) => ())
        )

        // We want to allow covariant unless the values are leased.
        // We do that by allowing it if the target type is `copy` or `my`.
        //
        // Here we rule out any form of variance (relative, atomic) and
        // limit that to invariant. This is stricter than needed.


        (
            (if perms_b.is_copy(&env))
            (sub_under_perms(&env, &live_after, &perms_a, &a, &perms_b, &b) => ())
            ------------------------------- ("covariant-copy")
            (sub_generic_parameter(env, live_after, (), perms_a, a, perms_b, b) => ())
        )


        (
            (if perms_b.is_owned(&env))
            (sub_under_perms(&env, &live_after, &perms_a, &a, &perms_b, &b) => ())
            ------------------------------- ("covariant-owned")
            (sub_generic_parameter(env, live_after, (), perms_a, a, perms_b, b) => ())
        )
    }
}

trait Implies {
    fn implies(self, other: bool) -> bool;
}

impl Implies for bool {
    fn implies(self, other: bool) -> bool {
        !self || (self && other)
    }
}

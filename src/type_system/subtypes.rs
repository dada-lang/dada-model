use formality_core::{judgment_fn, Cons, Set};

use crate::{
    dada_lang::grammar::UniversalVar,
    grammar::{NamedTy, Parameter, Place},
    type_system::{
        env::Env,
        flow::Flow,
        quantifiers::fold_zipped,
        terms::{terms_in, Terms},
    },
};

judgment_fn! {
    pub fn sub(
        env: Env,
        flow: Flow,
        a: Parameter,
        b: Parameter,
    ) => (Env, Flow) {
        debug(a, b, env, flow)

        (
            (sub_in(env, flow, Terms::default(), a, Terms::default(), b) => (env, flow))
            ------------------------------- ("sub")
            (sub(env, flow, a, b) => (env, flow))
        )
    }
}

judgment_fn! {
    pub fn sub_in(
        env: Env,
        flow: Flow,
        terms_a: Terms,
        a: Parameter,
        terms_b: Terms,
        b: Parameter,
    ) => (Env, Flow) {
        debug(terms_a, a, terms_b, b, env, flow)

        (
            (terms_in(env, terms_a0, a) => (env, terms_a1))
            (terms_in(env, &terms_b0, &b) => (env, terms_b1))
            (sub_terms(env, &flow, &terms_a1, terms_b1) => (env, flow))
            ------------------------------- ("sub")
            (sub_in(env, flow, terms_a0, a, terms_b0, b) => (env, flow))
        )
    }
}

judgment_fn! {
    pub fn sub_terms(
        env: Env,
        flow: Flow,
        terms_a: Terms,
        terms_b: Terms,
    ) => (Env, Flow) {
        debug(terms_a, terms_b, env, flow)

        (
            (if terms_a.shared < terms_b.shared)
            (if terms_a.leased < terms_b.leased)
            (if terms_a.liens.is_subset(&terms_b.liens))
            (sub_forall_exists(env, &flow, &terms_a.vars, &terms_b.vars) => (env, flow))
            (sub_forall_exists(env, flow, &terms_a.named_tys, &terms_b.named_tys) => (env, flow))
            ------------------------------- ("sub_teams")
            (sub_terms(env, flow, terms_a, terms_b) => (env, &flow))
        )
    }
}

judgment_fn! {
    pub fn sub_forall_exists(
        env: Env,
        flow: Flow,
        a_s: Set<(Terms, Parameter)>,
        b_s: Set<(Terms, Parameter)>,
    ) => (Env, Flow) {
        debug(a_s, b_s, env, flow)

        (
            ------------------------------- ("nil")
            (sub_forall_exists(env, flow, (), _b_s) => (env, flow))
        )

        (
            (&b_s => (terms_b, p_b))
            (sub_base(&env, &flow, &terms_a, &p_a, terms_b, p_b) => (env, flow))
            (sub_forall_exists(env, flow, &a_s, &b_s) => (env, flow))
            ------------------------------- ("cons")
            (sub_forall_exists(env, flow, Cons((terms_a, p_a), a_s), b_s) => (env, flow))
        )
    }
}

judgment_fn! {
    pub fn sub_base(
        env: Env,
        flow: Flow,
        terms_a: Terms,
        a: Parameter,
        terms_b: Terms,
        b: Parameter,
    ) => (Env, Flow) {
        debug(terms_a, a, terms_b, b, env, flow)

        (
            (if name_a == name_b)! // FIXME: subclassing
            (fold_zipped(
                (env, flow),
                parameters_a,
                parameters_b,
                // FIXME: variance
                &|(env, flow), p_a, p_b| sub_in(env, flow, &terms_a, p_a, &terms_b, p_b),
            ) => (env, flow))
            ------------------------------- ("named-types")
            (sub_base(
                env, flow,
                terms_a, NamedTy { name: name_a, parameters: parameters_a },
                terms_b, NamedTy { name: name_b, parameters: parameters_b },
            ) => (env, &flow))
        )

        (
            (if a == b)!
            (sub_terms(env, flow, terms_a, terms_b) => (env, flow))
            ------------------------------- ("universal variables")
            (sub_base(
                env, flow,
                terms_a, a: UniversalVar,
                terms_b, b: UniversalVar,
            ) => (env, &flow))
        )
    }
}

/// True if every place listed in `places` is "covered" by one of the places in
/// `covering_places`. A place P1 *covers* a place P2 if it is a prefix:
/// for example, `x.y` covers `x.y` and `x.y.z` but not `x.z` or `x1`.
fn all_places_covered_by_one_of(places: &Set<Place>, covering_places: &Set<Place>) -> bool {
    places
        .iter()
        .all(|place| place_covered_by_one_of(place, covering_places))
}

/// See [`all_places_covered_by_one_of`][].
#[tracing::instrument(level = "Debug", ret)]
fn place_covered_by_one_of(place: &Place, covering_places: &Set<Place>) -> bool {
    covering_places
        .iter()
        .any(|covering_place| place_covered_by_place(place, covering_place))
}

/// See [`all_places_covered_by_one_of`][].
#[tracing::instrument(level = "Debug", ret)]
fn place_covered_by_place(place: &Place, covering_place: &Place) -> bool {
    place.var == covering_place.var
        && place.projections.len() >= covering_place.projections.len()
        && place
            .projections
            .iter()
            .zip(&covering_place.projections)
            .all(|(proj1, proj2)| proj1 == proj2)
}

#[cfg(test)]
mod tests;

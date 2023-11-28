use formality_core::{cast_impl, judgment_fn, seq, set, Cons, Downcast, Set, Upcast};

use crate::{
    dada_lang::grammar::Variable,
    grammar::{ClassTy, Parameter, Perm, Place, Predicate, Ty},
    type_system::env::Env,
};

judgment_fn! {
    pub fn sub(
        env: Env,
        a: Parameter,
        b: Parameter,
    ) => Env {
        debug(a, b, env)

        trivial(a == b => env)

        // --------------------------------------------------------------------
        // Collapse rule
        //
        // This rules simplifies types that have more than one layer of permissions.
        // For example a `shared(a) shared(b) String` is equivalent to a `shared(b) String`,
        // and a `leased(a) leased(b) String` is equivalent to a `leased(a) String`.

        (
            (collapse(env, a) => (env, a1))
            (collapse(&env, b) => (env, b1))
            (sub(env, &a1, b1) => env)
            ---------------------- ("collapse a or b")
            (sub(env, a: Ty, b: Ty) => env)
        )

        // --------------------------------------------------------------------
        // Subclassing and so on
        //
        // These rules augment the trivial identity rule (above) with ways to relate
        // types that are not syntactically identical.

        (
            (if name_a == name_b)
            (suball(env, parameters_a, parameters_b) => env) // FIXME: variance
            ---------------------- ("same class")
            (sub(env, ClassTy { name: name_a, parameters: parameters_a }, ClassTy { name: name_b, parameters: parameters_b }) => env)
        )

        // FIXME: upcasting between classes

        // --------------------------------------------------------------------
        // Place subset
        //
        // These rules augment the trivial identity rule (above) with ways to relate
        // permissions that are not syntactically identical.

        (
            (if all_places_covered_by_one_of(&places_a, &places_b))
            ---------------------- ("shared perms")
            (sub(env, Perm::Shared(places_a), Perm::Shared(places_b)) => env)
        )

        (
            (if all_places_covered_by_one_of(&places_a, &places_b))
            ---------------------- ("leased perms")
            (sub(env, Perm::Leased(places_a), Perm::Leased(places_b)) => env)
        )

        (
            (if all_places_covered_by_one_of(&places_a, &places_b))
            ---------------------- ("owned perms")
            (sub(env, Perm::Given(places_a), Perm::Given(places_b)) => env)
        )

        // Somewhat debatable to me if we want this rule or if we want some outer rule
        // that accommodates *coerions*.
        //
        // In particular, `is_shared` becomes rather more complicated?
        //
        // *But* this rule would allow `Vec<String>` to be a subtype of `Vec<shared(a) String>`...
        // ...
        (
            (is_owned(env, a) => env)
            (is_shared(env, b) => env)
            ---------------------- ("owned, shared perms")
            (sub(env, a: Perm, b: Perm) => env)
        )
    }
}

judgment_fn! {
    fn collapse(
        env: Env,
        a: Ty,
    ) => (Env, Ty) {
        debug(a, env)

        (
            ---------------------- ("identity")
            (collapse(env, p) => (env, p))
        )

        (
            (collapse(env, &*a) => (env, b))
            (is_shared(env, &b) => env)
            ---------------------- ("(_ shared) => shared")
            (collapse(env, Ty::ApplyPerm(_, a)) => (env, b))
        )

        (
            (is_leased(env, &p) => env)
            (collapse(env, &*a) => (env, b))
            (if let Some(Ty::ApplyPerm(q, b)) = b.downcast())
            (is_leased(env, q) => env)
            ---------------------- ("(leased(a) leased(b)) => leased(a)")
            (collapse(env, Ty::ApplyPerm(p, a)) => (env, Ty::apply_perm(&p, &*b)))
        )

        (
            (is_owned(env, &p) => env)
            (collapse(env, &*a) => (env, b))
            ---------------------- ("(given() P) => P")
            (collapse(env, Ty::ApplyPerm(p, a)) => (env, b))
        )
    }
}

judgment_fn! {
    pub fn suball(
        env: Env,
        a_s: Vec<Parameter>,
        b_s: Vec<Parameter>,
    ) => Env {
        debug(a_s, b_s, env)
        (
            ---------------------- ("nil")
            (suball(env, (), ()) => env)
        )


        (
            (sub(env, head_a, head_b) => env)
            (suball(env, tail_a, tail_b) => env)
            ---------------------- ("types")
            (suball(env, Cons(head_a, tail_a), Cons(head_b, tail_b)) => env)
        )
    }
}

judgment_fn! {
    fn is_owned(
        env: Env,
        a: Perm,
    ) => Env {
        debug(a, env)

        (
            (if places.is_empty())
            ---------------------- ("given-perm")
            (is_owned(env, Perm::Given(places)) => env)
        )


        (
            (if env.contains_assumption(Predicate::owned(v)))
            ---------------------- ("universal")
            (is_owned(env, Variable::UniversalVar(v)) => env)
        )

        // FIXME: existential variables can be known to be shared-- what to do about *that*?
    }
}

judgment_fn! {
    fn is_leased(
        env: Env,
        a: Parameter,
    ) => Env {
        debug(a, env)

        (
            (is_leased(env, perm) => env)
            ---------------------- ("apply-perm")
            (is_leased(env, Ty::ApplyPerm(perm, _)) => env)
        )

        (
            ---------------------- ("leased-perm")
            (is_leased(env, Perm::Leased(..)) => env)
        )

        (
            (if env.contains_assumption(Predicate::leased(v)))
            ---------------------- ("universal")
            (is_leased(env, Variable::UniversalVar(v)) => env)
        )

        // FIXME: existential variables can be known to be shared-- what to do about *that*?
    }
}

judgment_fn! {
    fn is_shared(
        env: Env,
        a: Parameter,
    ) => Env {
        debug(a, env)

        (
            (is_shared(env, perm) => env)
            ---------------------- ("apply-perm")
            (is_shared(env, Ty::ApplyPerm(perm, _)) => env)
        )

        (
            ---------------------- ("shared-perm")
            (is_shared(env, Perm::Shared(..)) => env)
        )

        (
            (if env.contains_assumption(Predicate::shared(v)))
            ---------------------- ("universal")
            (is_shared(env, Variable::UniversalVar(v)) => env)
        )

        // FIXME: existential variables can be known to be shared-- what to do about *that*?
    }
}

/// True if every place listed in `places` is "covered" by one of the places in
/// `covering_places`. A place P1 *covers* a place P2 if it is a prefix:
/// for example, `x.y` covers `x.y` and `x.y.z` but not `x.z` or `x1`.
fn all_places_covered_by_one_of(places: &[Place], covering_places: &[Place]) -> bool {
    places
        .iter()
        .all(|place| place_covered_by_one_of(place, covering_places))
}

/// See [`all_places_covered_by_one_of`][].
#[tracing::instrument(level = "Debug", ret)]
fn place_covered_by_one_of(place: &Place, covering_places: &[Place]) -> bool {
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

use formality_core::{cast_impl, judgment_fn, set, Cons, Set, Upcast};

use crate::{
    grammar::{ClassTy, Parameter, Perm, Place, Ty},
    type_system::env::Env,
};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct SubResult {
    env: Env,
    cancels: Set<Place>,
}

cast_impl!(SubResult);

impl SubResult {
    fn new(env: impl Upcast<Env>, cancels: impl Upcast<Set<Place>>) -> Self {
        SubResult {
            env: env.upcast(),
            cancels: cancels.upcast(),
        }
    }
}

judgment_fn! {
    pub fn sub(
        env: Env,
        a: Parameter,
        b: Parameter,
    ) => SubResult {
        debug(a, b, env)

        trivial(a == b => SubResult::new(env, ()))

        (
            (if name_a == name_b)
            (suball(env, parameters_a, parameters_b) => result)
            ---------------------- ("types")
            (sub(env, ClassTy { name: name_a, parameters: parameters_a }, ClassTy { name: name_b, parameters: parameters_b }) => result)
        )

        (
            (if all_places_covered_by_one_of(&places_a, &places_b))
            ---------------------- ("shared perms")
            (sub(env, Perm::Shared(places_a), Perm::Shared(places_b)) => SubResult::new(env, ()))
        )

        (
            (if all_places_covered_by_one_of(&places_a, &places_b))
            ---------------------- ("leased perms")
            (sub(env, Perm::Leased(places_a), Perm::Leased(places_b)) => SubResult::new(env, ()))
        )

        (
            (if all_places_covered_by_one_of(&places_a, &places_b))
            ---------------------- ("owned perms")
            (sub(env, Perm::Given(places_a), Perm::Given(places_b)) => SubResult::new(env, ()))
        )

        (
            (if places_a.is_empty())
            ---------------------- ("owned, shared perms")
            (sub(env, Perm::Given(places_a), Perm::Shared(_)) => SubResult::new(env, ()))
        )

        (
            (cancel_path(env, a) => (a1, cancels_a))
            (sub(env, a1, b) => SubResult { env, cancels })
            --- ("cancel a")
            (sub(env, a: Perm, b: Perm) => SubResult::new(env, (cancels, cancels_a)))
        )

        (
            (cancel_path(env, b) => (b1, cancels_b))
            (sub(env, a, b1) => SubResult { env, cancels })
            --- ("cancel b")
            (sub(env, a: Perm, b: Perm) => SubResult::new(env, (cancels, cancels_b)))
        )
    }
}

judgment_fn! {
    pub fn suball(
        env: Env,
        a_s: Vec<Parameter>,
        b_s: Vec<Parameter>,
    ) => SubResult {
        debug(a_s, b_s, env)
        (
            ---------------------- ("nil")
            (suball(env, (), ()) => SubResult { env, cancels: set![] })
        )


        (
            (sub(env, head_a, head_b) => SubResult { env, cancels: cancels_head })
            (suball(env, tail_a, tail_b) => SubResult { env, cancels: cancels_tail})
            ---------------------- ("types")
            (suball(env, Cons(head_a, tail_a), Cons(head_b, tail_b)) => SubResult { env, cancels: set![..cancels_head, ..cancels_tail] })
        )
    }
}

judgment_fn! {
    fn is_given(
        env: Env,
        a: Perm,
    ) => () {
        debug(a, env)

        (
            ---------------------- ("given-perm")
            (is_given(env, Perm::Given(..)) => ())
        )

        // FIXME: universal variables can be shared in the environment

        // FIXME: existential variables can be known to be shared-- what to do about *that*?
    }
}

judgment_fn! {
    fn is_leased(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (is_leased(env, perm) => ())
            ---------------------- ("apply-perm")
            (is_leased(env, Ty::ApplyPerm(perm, _)) => ())
        )

        (
            ---------------------- ("leased-perm")
            (is_leased(env, Perm::Leased(..)) => ())
        )

        // FIXME: universal variables can be shared in the environment

        // FIXME: existential variables can be known to be shared-- what to do about *that*?
    }
}

judgment_fn! {
    fn is_shared(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (is_shared(env, perm) => ())
            ---------------------- ("apply-perm")
            (is_shared(env, Ty::ApplyPerm(perm, _)) => ())
        )

        (
            ---------------------- ("shared-perm")
            (is_shared(env, Perm::Shared(..)) => ())
        )

        // FIXME: universal variables can be shared in the environment

        // FIXME: existential variables can be known to be shared-- what to do about *that*?
    }
}

judgment_fn! {
    fn cancel_path(
        env: Env,
        perm: Perm,
    ) => (Perm, Set<Place>) {
        debug(perm, env)

        // FIXME: implement
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

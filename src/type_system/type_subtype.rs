use anyhow::bail;
use contracts::requires;
use formality_core::{cast_impl, judgment_fn, set, Cons, Fallible, Set, Upcast};

use crate::{
    dada_lang::grammar::{UniversalVar, Variable},
    grammar::{ClassTy, Parameter, Perm, Place, Ty},
    type_system::env::Env,
};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct SubResult {
    env: Env,
    cancels: Set<Place>,
}

cast_impl!(SubResult);

judgment_fn! {
    pub fn subparameters(
        env: Env,
        a: Parameter,
        b: Parameter,
    ) => SubResult {
        debug(a, b, env)

        (
            (subtypes(env, a.simplify(), b.simplify()) => result)
            ---------------------- ("types")
            (subparameters(env, Parameter::Ty(a), Parameter::Ty(b)) => result)
        )
    }
}

judgment_fn! {
    fn subparameterlists(
        env: Env,
        a: Vec<Parameter>,
        b: Vec<Parameter>,
    ) => SubResult {
        debug(a, b, env)

        (
            ---------------------- ("none")
            (subparameterlists(env, (), ()) => SubResult { env, cancels: set![] })
        )

        (
            (subparameters(env, param_a, param_b) => SubResult { env, cancels: cancels1 })
            (subparameterlists(env, params_a, params_b) => SubResult { env, cancels: cancels2 })
            ---------------------- ("some")
            (subparameterlists(env, Cons(param_a, params_a), Cons(param_b, params_b)) => SubResult { env, cancels: set![..cancels1, ..cancels2] })
        )
    }
}

judgment_fn! {
    fn subtypes(
        env: Env,
        a: Ty,
        b: Ty,
    ) => SubResult {
        debug(a, b, env)
        assert(a.is_simplified() && matches!(a, Ty::ApplyPerm(..)))
        assert(b.is_simplified() && matches!(b, Ty::ApplyPerm(..)))

        trivial(a == b => SubResult { env, cancels: set![] })

        (
            (subperms(env, perm_a, perm_b) => SubResult { env, cancels: cancels1 })
            (subtypeatoms(env, &*ty_a, &*ty_b) => SubResult { env, cancels: cancels2 })
            --- ("subtypes")
            (subtypes(env, Ty::ApplyPerm(perm_a, ty_a), Ty::ApplyPerm(perm_b, ty_b)) => SubResult { env, cancels: (cancels1, cancels2).upcast() })
        )
    }
}

judgment_fn! {
    fn subtypeatoms(
        env: Env,
        a: Ty,
        b: Ty,
    ) => SubResult {
        debug(a, b, env)
        assert(!matches!(a, Ty::ApplyPerm(..)))
        assert(!matches!(b, Ty::ApplyPerm(..)))

        trivial(a == b => SubResult { env, cancels: set![] })

        (
            (if name_a == name_b)
            (subparameterlists(env, parameters_a, parameters_b) => result)
            --- ("class types")
            (subtypeatoms(env, ClassTy { name: name_a, parameters: parameters_a }, ClassTy { name: name_b, parameters: parameters_b }) => result)
        )

        // FIXME: existential variables

        (
            (if a == b)
            --- ("universal variables")
            (subtypeatoms(env, Variable::UniversalVar(a), Variable::UniversalVar(b)) => SubResult { env, cancels: set![] })
        )
    }
}

judgment_fn! {
    fn subperms(
        env: Env,
        a: Perm,
        b: Perm,
    ) => SubResult {
        debug(a, b, env)
        assert(a.is_simplified())
        assert(b.is_simplified())

        (
            (cancel_path(env, a) => (a1, cancels_a))
            (subperms(env, a1, b) => SubResult { env, cancels })
            --- ("cancel a")
            (subperms(env, a, b) => SubResult { env, cancels: (cancels, cancels_a).upcast() })
        )

        (
            (cancel_path(env, b) => (b1, cancels_b))
            (subperms(env, a, b1) => SubResult { env, cancels })
            --- ("cancel b")
            (subperms(env, a, b) => SubResult { env, cancels: (cancels, cancels_b).upcast() })
        )

        (
            --- ("owned <: shared")
            (subperms(env, Perm::Owned, Perm::Shared(..)) => SubResult { env, cancels: set![] })
        )

        (
            --- ("owned <: owned")
            (subperms(env, Perm::Owned, Perm::Owned) => SubResult { env, cancels: set![] })
        )

        (
            (suborigins(env, a, b) => env)
            --- ("shared <: shared")
            (subperms(env, a @ Perm::Shared(..), b @ Perm::Shared(..)) => SubResult { env, cancels: set![] })
        )

        (
            (suborigins(env, a, b) => env)
            --- ("shared <: shared")
            (subperms(env, a @ Perm::Leased(..), b @ Perm::Leased(..)) => SubResult { env, cancels: set![] })
        )

        // FIXME: existential variables

        (
            (suborigins(env, a, b) => env)
            --- ("uvar <: uvar")
            (subperms(env, a @ Perm::Var(Variable::UniversalVar(_), _), b @ Perm::Var(Variable::UniversalVar(_), _)) => SubResult { env, cancels: set![] })
        )
    }
}

judgment_fn! {
    fn suborigins(
        env: Env,
        a: Perm,
        b: Perm,
    ) => Env {
        debug(a, b, env)
        assert(a.is_simplified())
        assert(b.is_simplified())

        trivial(a == b => env)

        (
            --- ("_ <: owned")
            (suborigins(env, _a, Perm::Owned) => env)
        )

        (
            (require_all_places_covered_by_one_of(&a_places, &b_places) => ())
            (suborigins(env, &*origin_a, &*origin_b) => env)
            --- ("shared <: shared")
            (suborigins(env, Perm::Shared(a_places, origin_a), Perm::Shared(b_places, origin_b)) => env)
        )

        (
            (require_all_places_covered_by_one_of(&a_places, &b_places) => ())
            (suborigins(env, &*origin_a, &*origin_b) => env)
            --- ("leased <: leased")
            (suborigins(env, Perm::Leased(a_places, origin_a), Perm::Leased(b_places, origin_b)) => env)
        )

        // FIXME: existential variables

        (
            (if var_a == var_b) // FIXME: consult environment
            (suborigins(env, &*origin_a, &*origin_b) => env)
            --- ("uvar <: uvar")
            (suborigins(env, Perm::Var(Variable::UniversalVar(var_a), origin_a), Perm::Var(Variable::UniversalVar(var_b), origin_b)) => env)
        )
    }
}

judgment_fn! {
    fn cancel_path(
        env: Env,
        perm: Perm,
    ) => (Perm, Set<Place>) {
        debug(perm, env)

        (
            (is_not_owned(env, &*origin) => ())
            ------------------------------------------- ("shared")
            (cancel_path(env, Perm::Shared(places, origin)) => (&*origin, to_set(&places)))
        )

        (
            (is_not_owned(env, &*origin) => ())
            ------------------------------------------- ("leased")
            (cancel_path(env, Perm::Leased(places, origin)) => (&*origin, to_set(&places)))
        )
    }
}

// FIXME: we should make Shared etc take sets
fn to_set(v: &Vec<Place>) -> Set<Place> {
    v.iter().cloned().collect()
}

judgment_fn! {
    fn is_not_owned(
        env: Env,
        perm: Perm,
    ) => () {
        debug(perm, env)

        // FIXME: check the environment for universal variables

        // FIXME: check the environment for existential variables

        (
            ------------------------------------------- ("shared is not owned")
            (is_not_owned(env, Perm::Shared(..)) => ())
        )

        (
            ------------------------------------------- ("leased is not owned")
            (is_not_owned(env, Perm::Leased(..)) => ())
        )
    }
}

/// True if every place listed in `places` is "covered" by one of the places in
/// `covering_places`. A place P1 *covers* a place P2 if it is a prefix:
/// for example, `x.y` covers `x.y` and `x.y.z` but not `x.z` or `x1`.
fn require_all_places_covered_by_one_of(
    places: &[Place],
    covering_places: &[Place],
) -> Fallible<()> {
    for place in places {
        if !place_covered_by_one_of(place, covering_places) {
            bail!("`{place:?}` not covered by one of `{covering_places:?}`")
        }
    }
    Ok(())
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

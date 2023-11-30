use formality_core::{judgment_fn, Downcast, Set};

use crate::{
    dada_lang::grammar::{ExistentialVar, Variable},
    grammar::{ClassTy, Parameter, Perm, Place, Predicate, Ty},
    type_system::quantifiers::fold,
    type_system::{
        env::{Env, Existential, PermBound},
        quantifiers::fold_zipped,
    },
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
        // Relationships between types with permissions

        (
            (equivalent(env, a) => (env, a1))
            (equivalent(&env, &b) => (env, b1))
            (sub(env, &a1, b1) => env)
            ---------------------- ("collapse a or b")
            (sub(env, a: Ty, b: Ty) => env)
        )

        (
            (sub(env, perm_a, perm_b) => env)
            (sub(env, &*ty_a, &*ty_b) => env)
            ---------------------- ("apply-perms")
            (sub(env, Ty::ApplyPerm(perm_a, ty_a), Ty::ApplyPerm(perm_b, ty_b)) => env)
        )

        // --------------------------------------------------------------------
        // Subclassing and so on

        (
            (if name_a == name_b)
            (fold_zipped(env, parameters_a, parameters_b, &|env, a, b| sub(env, a, b)) => env) // FIXME: variance
            ---------------------- ("same class")
            (sub(env, ClassTy { name: name_a, parameters: parameters_a }, ClassTy { name: name_b, parameters: parameters_b }) => env)
        )

        // FIXME: upcasting between classes

        // --------------------------------------------------------------------
        // Place subset

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

        // --------------------------------------------------------------------
        // Given/Shared subpermissions
        //
        // Owned types are subtypes of shared ones: the representation is the same
        // and all operations legal on shared values are supported on owned ones.

        (
            (is_owned(env, a) => env)
            (is_shared(env, &b) => env)
            ---------------------- ("owned, shared perms")
            (sub(env, a: Perm, b: Perm) => env)
        )

        // --------------------------------------------------------------------
        // Existential variables
        //
        // Owned types are subtypes of shared ones: the representation is the same
        // and all operations legal on shared values are supported on owned ones.

        (
            (if env.has_lower_bound(lower_bound, var))
            ---------------------- ("existential, lower-bounded")
            (sub(env, lower_bound, var: ExistentialVar) => env)
        )

        (
            (if env.has_upper_bound(var, upper_bound))
            ---------------------- ("existential, upper-bounded")
            (sub(env, var: ExistentialVar, upper_bound) => env)
        )

        (
            (env.with(|env| env.new_lower_bound(&lower_bound, var)) => env)
            (let Existential { universe: _, kind: _, lower_bounds: _, upper_bounds, perm_bound } = env.existential(var).clone())
            (fold(env, perm_bound, &|env, b| lower_bound_meets_perm_bound(env, &lower_bound, b)) => env)
            // (fold(env, lower_bounds, &|env, other_lower_bound| compatible(env, &lower_bound, other_lower_bound)) => env)
            (fold(env, &upper_bounds, &|env, upper_bound| sub(env, &lower_bound, upper_bound)) => env)
            ---------------------- ("existential, lower-bounded")
            (sub(env, lower_bound, var: ExistentialVar) => env)
        )

        (
            (env.with(|env| env.new_upper_bound(var, &upper_bound)) => env)
            (let Existential { universe: _, kind: _, lower_bounds, upper_bounds: _, perm_bound } = env.existential(var).clone())
            (fold(env, perm_bound, &|env, b| upper_bound_meets_perm_bound(env, b, &upper_bound)) => env)
            (fold(env, &lower_bounds, &|env, lower_bound| sub(env, lower_bound, &upper_bound)) => env)
            // (fold(env, upper_bounds, &|env, other_upper_bound| compatible(env, &upper_bound, other_upper_bound)) => env)
            ---------------------- ("existential, upper-bounded")
            (sub(env, var: ExistentialVar, upper_bound) => env)
        )
    }
}

judgment_fn! {
    /// Produces equivalent versions of a type, primarily by simplifying permissions.
    /// For example a `shared(a) shared(b) String` is equivalent to a `shared(b) String`,
    /// and a `leased(a) leased(b) String` is equivalent to a `leased(a) String`.
    /// Does in some case introduce permisions, e.g. the class type `Foo` and
    /// `given{} Foo` are equivalent.
    fn equivalent(
        env: Env,
        a: Ty,
    ) => (Env, Ty) {
        debug(a, env)

        (
            ---------------------- ("identity")
            (equivalent(env, p) => (env, p))
        )

        (
            ---------------------- ("identity")
            (equivalent(env, c: ClassTy) => (env, Ty::apply_perm(Perm::given(()), c)))
        )

        (
            (equivalent(env, &*a) => (env, b))
            (is_shared(env, &b) => env)
            ---------------------- ("(_ shared) => shared")
            (equivalent(env, Ty::ApplyPerm(_, a)) => (env, &b))
        )

        (
            (is_leased(env, &p) => env)
            (equivalent(env, &*a) => (env, b))
            (if let Some(Ty::ApplyPerm(q, b)) = b.downcast())
            (is_leased(env, q) => env)
            ---------------------- ("(leased(a) leased(b)) => leased(a)")
            (equivalent(env, Ty::ApplyPerm(p, a)) => (env, Ty::apply_perm(&p, &*b)))
        )

        (
            (is_owned(env, &p) => env)
            (equivalent(env, &*a) => (env, b))
            ---------------------- ("(given() owned) => owned")
            (equivalent(env, Ty::ApplyPerm(p, a)) => (env, b))
        )
    }
}

judgment_fn! {
    fn upper_bound_meets_perm_bound(
        env: Env,
        bound: PermBound,
        upper_bound: Parameter,
    ) => Env {
        debug(bound, upper_bound, env)

        (
            (is_owned(env, upper_bound) => env)
            ---------------------- ("owned")
            (upper_bound_meets_perm_bound(env, PermBound::Owned, upper_bound) => env)
        )

        (
            (is_leased(env, upper_bound) => env)
            ---------------------- ("leased")
            (upper_bound_meets_perm_bound(env, PermBound::Leased, upper_bound) => env)
        )

        (
            (is_shared(env, upper_bound) => env)
            ---------------------- ("shared")
            (upper_bound_meets_perm_bound(env, PermBound::Shared, upper_bound) => env)
        )
    }
}

judgment_fn! {
    fn lower_bound_meets_perm_bound(
        env: Env,
        lower_bound: Parameter,
        bound: PermBound,
    ) => Env {
        debug(bound, lower_bound, env)

        (
            (is_owned(env, lower_bound) => env)
            ---------------------- ("owned")
            (lower_bound_meets_perm_bound(env, lower_bound, PermBound::Owned) => env)
        )

        (
            (is_leased(env, lower_bound) => env)
            ---------------------- ("leased")
            (lower_bound_meets_perm_bound(env, lower_bound, PermBound::Leased) => env)
        )

        (
            (is_shared(env, lower_bound) => env)
            ---------------------- ("shared")
            (lower_bound_meets_perm_bound(env, lower_bound, PermBound::Shared) => env)
        )

        (
            (is_owned(env, lower_bound) => env)
            ---------------------- ("shared")
            (lower_bound_meets_perm_bound(env, lower_bound, PermBound::Shared) => env)
        )
    }
}

judgment_fn! {
    /// A parameter `a` is **owned** if it represents unique ownership.
    /// This is only true for a narrow range of things.
    ///
    /// It's only truly used on permisions, but we define it for all parameters
    /// because that makes the code prettier and there's no reason not to.
    ///
    /// For permisions: only `given{}` is owned. `given{a}` doesn't count
    /// because it is given *from* `a` (which may not be owned).
    ///
    /// For types: only class types are owned, not type variables, as type variables
    /// may represent all kinds of things (unless of course we have something
    /// in the environment).
    fn is_owned(
        env: Env,
        a: Parameter,
    ) => Env {
        debug(a, env)

        (
            ---------------------- ("class types are owned")
            (is_owned(env, _c: ClassTy) => env)
        )

        (
            (is_owned(env, p) => env)
            (is_owned(env, &*t) => env)
            ---------------------- ("class types are owned")
            (is_owned(env, Ty::ApplyPerm(p, t)) => env)
        )

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

        (
            (if env.has_perm_bound(v, PermBound::Owned))
            ---------------------- ("existential, bounded")
            (is_owned(env, Variable::ExistentialVar(v)) => env)
        )

        (
            (env.with(|env| env.new_perm_bound(v, PermBound::Owned)) => env)
            (let Existential { universe: _, kind: _, lower_bounds, upper_bounds, perm_bound: _ } = env.existential(v).clone())
            (fold(env, &lower_bounds, &|env, b| is_owned(env, b)) => env)
            (fold(env, &upper_bounds, &|env, b| is_owned(env, b)) => env)
            ---------------------- ("existential")
            (is_owned(env, Variable::ExistentialVar(v)) => env)
        )
    }
}

judgment_fn! {
    /// A parameter `a` is **leased** when it represents exclusive access to
    /// the original object.
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

        (
            (if env.has_perm_bound(v, PermBound::Leased))
            ---------------------- ("existential, bounded")
            (is_leased(env, Variable::ExistentialVar(v)) => env)
        )

        (
            (env.with(|env| env.new_perm_bound(v, PermBound::Leased)) => env)
            (let Existential { universe: _, kind: _, lower_bounds, upper_bounds, perm_bound: _ } = env.existential(v).clone())
            (fold(env, lower_bounds, &|env, b| is_leased(env, b)) => env)
            (fold(env, &upper_bounds, &|env, b| is_leased(env, b)) => env)
            ---------------------- ("existential")
            (is_leased(env, Variable::ExistentialVar(v)) => env)
        )
    }
}

judgment_fn! {
    /// A parameter `a` is **shared** when it represents shared access to
    /// the original object (specifically, the lack of unique access).
    /// Note that owned types are subtypes of shared types,
    /// but they are not *shared*, because they have unique access
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

        (
            (if env.has_perm_bound(v, PermBound::Shared))
            ---------------------- ("existential, bounded")
            (is_shared(env, Variable::ExistentialVar(v)) => env)
        )

        (
            (env.with(|env| env.new_perm_bound(v, PermBound::Shared)) => env)
            (let Existential { universe: _, kind: _, lower_bounds, upper_bounds, perm_bound: _ } = env.existential(v).clone())
            (fold(env, lower_bounds, &|env, b| is_shared(env, b)) => env)
            (fold(env, &upper_bounds, &|env, b| is_shared(env, b)) => env)
            ---------------------- ("existential, unbounded")
            (is_shared(env, Variable::ExistentialVar(v)) => env)
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

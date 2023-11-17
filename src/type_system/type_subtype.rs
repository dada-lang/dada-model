use formality_core::judgment_fn;

use crate::{
    grammar::{ClassTy, Parameter, Perm, Place, Program, Ty},
    type_system::{env::Env, quantifiers::fold_zipped},
};

judgment_fn! {
    pub fn sub(
        program: Program,
        env: Env,
        a: Parameter,
        b: Parameter,
    ) => Env {
        debug(a, b, program, env)

        trivial(a == b => env)

        (
            (subtype(program, env, sub.simplify(), sup.simplify()) => env)
            --------------------------- ("int")
            (sub(program, env, Parameter::Ty(sub), Parameter::Ty(sup)) => env)
        )

        (
            (subperm(program, env, sub.simplify(), sup.simplify()) => env)
            --------------------------- ("perm")
            (sub(program, env, Parameter::Perm(sub), Parameter::Perm(sup)) => env)
        )
    }
}

judgment_fn! {
    fn subtype(
        program: Program,
        env: Env,
        a: Ty,
        b: Ty,
    ) => Env {
        debug(a, b, program, env)
        assert(a.is_simplified())
        assert(b.is_simplified())

        trivial(a == b => env)

        (
            (if name_a == name_b)
            // FIXME: variance
            (fold_zipped(
                env,
                &parameters_a,
                &parameters_b,
                &|env, p_sub, p_sup| sub(&program, env, p_sub, p_sup)
            ) => env)
            --------------------------- ("class")
            (subtype(
                program,
                env,
                ClassTy { name: name_a, parameters: parameters_a },
                ClassTy { name: name_b, parameters: parameters_b }
            ) => env)
        )

        (
            (sub(&program, env, perm_a, perm_b) => env)
            (sub(&program, env, &*ty_a, &*ty_b) => env)
            --------------------------- ("applied")
            (subtype(
                program,
                env,
                Ty::ApplyPerm(perm_a, ty_a),
                Ty::ApplyPerm(perm_b, ty_b),
            ) => env)
        )
    }
}

judgment_fn! {
    fn subperm(
        program: Program,
        env: Env,
        a: Perm,
        b: Perm,
    ) => Env {
        debug(a, b, program, env)
        assert(a.is_simplified())
        assert(b.is_simplified())

        trivial(a == b => env)

        (
            (if all_places_covered_by_one_of(&places_a, &places_b))
            (subperm(program, env, &*perm_a, &*perm_b) => env)
            --------------------------- ("shared-shared")
            (subperm(
                program,
                env,
                Perm::Shared(places_a, perm_a),
                Perm::Shared(places_b, perm_b),
            ) => env)
        )

        (
            (subperm(program, env, Perm::Owned, &*perm_b) => env)
            --------------------------- ("owned-shared")
            (subperm(
                program,
                env,
                Perm::Owned,
                Perm::Shared(_, perm_b),
            ) => env)
        )

        (
            (if all_places_covered_by_one_of(&places_a, &places_b))
            (subperm(program, env, &*perm_a, &*perm_b) => env)
            --------------------------- ("leased-leased")
            (subperm(
                program,
                env,
                Perm::Leased(places_a, perm_a),
                Perm::Leased(places_b, perm_b),
            ) => env)
        )

        (
            (subperm(program, env, &*perm_a, perm_b) => env)
            --------------------------- ("drop-subleased")
            (subperm(
                program,
                env,
                Perm::Leased(_, perm_a),
                perm_b,
            ) => env)
        )
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
fn place_covered_by_one_of(place: &Place, covering_places: &[Place]) -> bool {
    covering_places
        .iter()
        .any(|covering_place| place_covered_by_place(place, covering_place))
}

/// See [`all_places_covered_by_one_of`][].
fn place_covered_by_place(place: &Place, covering_place: &Place) -> bool {
    place.var == covering_place.var
        && place
            .projections
            .iter()
            .zip(&covering_place.projections)
            .all(|(proj1, proj2)| proj1 == proj2)
}

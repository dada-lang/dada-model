use formality_core::judgment_fn;

use crate::{
    grammar::{ClassTy, Parameter, Perm, Place, Program, Ty},
    type_system::{env::Env, quantifiers::fold_zipped},
};

judgment_fn! {
    pub fn sub(
        program: Program,
        env: Env,
        sub: Parameter,
        sup: Parameter,
    ) => Env {
        debug(sub, sup, program, env)

        trivial(sub == sup => env)

        (
            (subtype(program, env, sub.simplify(), sup.simplify()) => env)
            --------------------------- ("int")
            (sub(program, env, Parameter::Ty(sub), Parameter::Ty(sup)) => env)
        )

        (
            (subperm(program, env, sub.simplify(), sup.simplify()) => env)
            --------------------------- ("int")
            (sub(program, env, Parameter::Perm(sub), Parameter::Perm(sup)) => env)
        )
    }
}

judgment_fn! {
    fn subtype(
        program: Program,
        env: Env,
        sub_ty: Ty,
        sup_ty: Ty,
    ) => Env {
        debug(sub_ty, sup_ty, program, env)
        assert(sub_ty.is_simplified())
        assert(sup_ty.is_simplified())

        trivial(sub_ty == sup_ty => env)

        (
            (if name_sub == name_sup)
            // FIXME: variance
            (fold_zipped(
                env,
                &parameters_sub,
                &parameters_sup,
                &|env, p_sub, p_sup| sub(&program, env, p_sub, p_sup)
            ) => env)
            --------------------------- ("class")
            (subtype(
                program,
                env,
                ClassTy { name: name_sub, parameters: parameters_sub },
                ClassTy { name: name_sup, parameters: parameters_sup }
            ) => env)
        )

        (
            (sub(&program, env, perm_sub, perm_sup) => env)
            (sub(&program, env, &*ty_sub, &*ty_sup) => env)
            --------------------------- ("applied")
            (subtype(
                program,
                env,
                Ty::ApplyPerm(perm_sub, ty_sub),
                Ty::ApplyPerm(perm_sup, ty_sup),
            ) => env)
        )
    }
}

judgment_fn! {
    fn subperm(
        program: Program,
        env: Env,
        sub: Perm,
        sup: Perm,
    ) => Env {
        debug(sub, sup, program, env)
        assert(sub.is_simplified())
        assert(sup.is_simplified())

        trivial(sub == sup => env)

        (
            (if all_places_covered_by_one_of(&places1, &places2))
            (subperm(program, env, &*perm1, &*perm2) => env)
            --------------------------- ("shared")
            (subperm(program, env, Perm::Shared(places1, perm1), Perm::Shared(places2, perm2)) => env)
        )

        (
            (if all_places_covered_by_one_of(&places1, &places2))
            (subperm(program, env, &*perm1, &*perm2) => env)
            --------------------------- ("leased")
            (subperm(program, env, Perm::Leased(places1, perm1), Perm::Leased(places2, perm2)) => env)
        )
    }
}

fn all_places_covered_by_one_of(places: &[Place], covering_places: &[Place]) -> bool {
    places
        .iter()
        .all(|place| place_covered_by_one_of(place, covering_places))
}

fn place_covered_by_one_of(place: &Place, covering_places: &[Place]) -> bool {
    covering_places
        .iter()
        .any(|covering_place| place_covered_by_place(place, covering_place))
}

fn place_covered_by_place(place: &Place, covering_place: &Place) -> bool {
    place.var == covering_place.var
        && place
            .projections
            .iter()
            .zip(&covering_place.projections)
            .all(|(proj1, proj2)| proj1 == proj2)
}

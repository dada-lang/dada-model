use formality_core::{judgment_fn, term, Set, SetExt};

use crate::{
    grammar::{NamedTy, Parameter, Perm, Place, Ty, Variable},
    type_system::{env::Env, predicates::prove_is_copy},
};

/// A lien on some data local to the current function.
/// This is a subset of the full [`Perm`] type that only
/// contains those variants relative to borrow checking.
// ANCHOR: Lien
#[term]
pub enum Lien {
    Rf(Place),
    Mt(Place),
}
// ANCHOR_END: Lien

judgment_fn! {
    /// Compute the liens required for a parameter `a` to be valid.
    pub fn liens(
        env: Env,
        a: Parameter,
    ) => Set<Lien> {
        debug(a, env)

        // PERMISSIONS
        // (Perm::Var covered under "VARIABLES" below)

        (
            ----------------------------------- ("perm-given")
            (liens(_env, Perm::Given) => ())
        )

        (
            ----------------------------------- ("perm-shared")
            (liens(_env, Perm::Shared) => ())
        )

        (
            (let liens: Set<Lien> = Set::new())
            (for_all(place in &places) with(liens)
                (place_liens(&env, (), &place) => new_liens)
                (let liens: Set<Lien> = (&liens).union_with(new_liens)))
            ----------------------------------- ("perm-given")
            (liens(env, Perm::Mv(places)) => liens)
        )

        (
            (let liens: Set<Lien> = Set::new())
            (for_all(place in &places) with(liens)
                (place_liens(&env, (Lien::rf(&place),), &place) => new_liens)
                (let liens: Set<Lien> = (&liens).union_with(new_liens)))
            ----------------------------------- ("perm-shared")
            (liens(env, Perm::Rf(places)) => liens)
        )

        (
            (let liens: Set<Lien> = Set::new())
            (for_all(place in &places) with(liens)
                (place_liens(&env, (Lien::mt(&place),), &place) => new_liens)
                (let liens: Set<Lien> = (&liens).union_with(new_liens)))
            ----------------------------------- ("perm-leased")
            (liens(env, Perm::Mt(places)) => liens)
        )

        (
            (liens(&env, &*lhs) => liens_lhs)
            (apply_liens(&env, liens_lhs, &*rhs) => liens)
            ----------------------------------- ("perm-apply")
            (liens(env, Perm::Apply(lhs, rhs)) => liens)
        )

        // TYPES
        // (Ty::Var covered under "VARIABLES" below)

        (
            (let liens_parameters: Set<Lien> = Set::new())
            (for_all(parameter in &parameters) with(liens_parameters)
                (liens(&env, &parameter) => new_liens)
                (let liens_parameters: Set<Lien> = (&liens_parameters).union_with(new_liens)))
            ----------------------------------- ("ty-named")
            (liens(env, NamedTy { name: _, parameters }) => liens_parameters)
        )

        (
            (liens(&env, lhs) => liens_lhs)
            (apply_liens(&env, liens_lhs, &*rhs) => liens)
            ----------------------------------- ("ty-apply-perm")
            (liens(env, Ty::ApplyPerm(lhs, rhs)) => liens)
        )

        // VARIABLES (either `Ty` or `Perm`)

        (
            ----------------------------------- ("!X")
            (liens(_env, Variable::UniversalVar(_)) => ())
        )
    }
}

judgment_fn! {
    fn place_liens(
        env: Env,
        liens_access: Set<Lien>,
        place: Place,
    ) => Set<Lien> {
        debug(liens_access, place, env)

        (
            (let ty = env.place_ty(&place)?)
            (liens(&env, ty) => liens)
            ----------------------------------- ("from type")
            (place_liens(env, liens_access, place) => (&liens_access, liens))
        )
    }
}

judgment_fn! {
    fn apply_liens(
        env: Env,
        liens_lhs: Set<Lien>,
        rhs: Parameter,
    ) => Set<Lien> {
        debug(liens_lhs, rhs, env)

        (
            (liens(&env, rhs) => liens_rhs)
            ----------------------------------- ("apply-not-copy")
            (apply_liens(env, liens_lhs, rhs) => (&liens_lhs, liens_rhs))
        )

        (
            (prove_is_copy(&env, &rhs) => ())
            (liens(&env, &rhs) => liens_rhs)
            ----------------------------------- ("apply-copy")
            (apply_liens(env, _liens_lhs, rhs) => liens_rhs)
        )
    }
}

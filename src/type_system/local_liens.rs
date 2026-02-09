use formality_core::{judgment_fn, term, Set};

use crate::{
    grammar::{NamedTy, Parameter, Perm, Place, Ty, Variable},
    type_system::{env::Env, predicates::prove_is_copy, quantifiers::union},
};

/// A lien on some data local to the current function.
/// This is a subset of the full [`Perm`] type that only
/// contains those variants relative to borrow checking.
#[term]
pub enum Lien {
    Rf(Place),
    Mt(Place),
}

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
            (union(&places, &|place| place_liens(&env, (), place)) => liens)
            ----------------------------------- ("perm-given")
            (liens(env, Perm::Mv(places)) => liens)
        )

        (
            (union(&places, &|place| place_liens(&env, (Lien::rf(place),), place)) => liens)
            ----------------------------------- ("perm-shared")
            (liens(env, Perm::Rf(places)) => liens)
        )

        (
            (union(&places, &|place| place_liens(&env, (Lien::mt(place),), place)) => liens)
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
            (union(parameters, &|parameter| liens(&env, parameter)) => liens_parameters)
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

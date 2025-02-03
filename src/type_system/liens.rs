use formality_core::{judgment_fn, term, Set};

use crate::{
    grammar::{NamedTy, Parameter, Place},
    type_system::{
        env::Env,
        quantifiers::union,
        red_terms::{red_terms, RedPerm, RedTerm, RedTy},
    },
};

/// A *lien* is a dependency that one place takes on another.
/// If `p1` has permission `shared[p2]`, then `p1` has a shared lien on `p2`,
/// which means that `p1` is permitted to share part of `p2` as long as it is in use,
/// which in turn means that `p2` is NOT permitted to be written to.
#[term]
pub enum Lien {
    Shared(Place),
    Leased(Place),
}

judgment_fn! {
    pub fn liens(
        env: Env,
        a: Parameter,
    ) => Set<Lien> {
        debug(a, env)

        (
            (red_terms(&env, RedPerm::my(), a) => red_terms_a)
            (union(red_terms_a, &|red_term_a| liens_from_red_term(&env, red_term_a)) => liens)
            ----------------------------------- ("my")
            (liens(env, a) => liens)
        )
    }
}

judgment_fn! {
    fn liens_from_red_term(
        env: Env,
        a: RedTerm,
    ) => Set<Lien> {
        debug(a, env)

        (
            (let liens_shared: Set<Lien> = perms.shared_from.iter().map(Lien::shared).collect())
            (let liens_leased: Set<Lien> = perms.leased_from.iter().map(Lien::leased).collect())
            (liens_from_red_ty(&env, ty) => liens_ty)
            ----------------------------------- ("rule")
            (liens_from_red_term(env, RedTerm { perms, ty }) => (&liens_shared, &liens_leased, liens_ty))
        )
    }
}

judgment_fn! {
    fn liens_from_red_ty(
        env: Env,
        a: RedTy,
    ) => Set<Lien> {
        debug(a, env)

        (
            ----------------------------------- ("none")
            (liens_from_red_ty(_env, RedTy::None) => ())
        )

        (
            ----------------------------------- ("var")
            (liens_from_red_ty(_env, RedTy::Var(_var)) => ())
        )

        (
            (union(parameters, &|parameter| liens(&env, parameter)) => liens)
            ----------------------------------- ("named")
            (liens_from_red_ty(_env, RedTy::NamedTy(NamedTy { name: _, parameters })) => liens)
        )
    }
}

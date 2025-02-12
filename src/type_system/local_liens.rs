use formality_core::{judgment_fn, set, term, Set};

use crate::{
    grammar::{NamedTy, Parameter, Place},
    type_system::{
        env::Env,
        quantifiers::union,
        red_terms::{red_term, Chain, Lien, RedPerm, RedTerm, RedTy},
    },
};

/// A lien on some data local to the current function.
/// This is a subset of the full [`Lien`] type that only
/// contains those variants relative to borrow checking.
#[term]
pub enum LocalLien {
    Shared(Place),
    Leased(Place),
}

judgment_fn! {
    pub fn local_liens(
        env: Env,
        a: Parameter,
    ) => Set<LocalLien> {
        debug(a, env)

        (
            (red_term(&env, a) => RedTerm { red_perm, red_ty })
            (local_liens_from_red_perm(&env, red_perm) => liens_1)
            (local_liens_from_red_ty(&env, &red_ty) => liens_2)
            ----------------------------------- ("my")
            (local_liens(env, a) => (&liens_1, liens_2))
        )
    }
}

judgment_fn! {
    fn local_liens_from_red_ty(
        env: Env,
        a: RedTy,
    ) => Set<LocalLien> {
        debug(a, env)

        (
            ----------------------------------- ("none")
            (local_liens_from_red_ty(_env, RedTy::None) => ())
        )

        (
            ----------------------------------- ("var")
            (local_liens_from_red_ty(_env, RedTy::Var(_var)) => ())
        )

        (
            (union(parameters, &|parameter| local_liens(&env, parameter)) => liens)
            ----------------------------------- ("named")
            (local_liens_from_red_ty(_env, RedTy::NamedTy(NamedTy { name: _, parameters })) => liens)
        )
    }
}

judgment_fn! {
    fn local_liens_from_red_perm(
        env: Env,
        a: RedPerm,
    ) => Set<LocalLien> {
        debug(a, env)

        (
            (union(chains, &|chain| local_liens_from_chain(&env, chain)) => liens)
            ----------------------------------- ("none")
            (local_liens_from_red_perm(_env, RedPerm { chains }) => liens)
        )
    }
}

judgment_fn! {
    fn local_liens_from_chain(
        env: Env,
        a: Chain,
    ) => Set<LocalLien> {
        debug(a, env)

        (
            (union(liens, &|lien| local_liens_from_lien(&env, lien)) => liens_out)
            ----------------------------------- ("none")
            (local_liens_from_chain(_env, Chain { liens }) => liens_out)
        )
    }
}

judgment_fn! {
    fn local_liens_from_lien(
        env: Env,
        a: Lien,
    ) => Set<LocalLien> {
        debug(a, env)

        (
            ----------------------------------- ("none")
            (local_liens_from_lien(_env, Lien::Our | Lien::Variable(_)) => ())
        )

        (
            (let place_ty = env.place_ty(&place)?)
            (local_liens(&env, place_ty) => liens)
            ----------------------------------- ("shared")
            (local_liens_from_lien(_env, Lien::Shared(place)) => set![LocalLien::shared(&place), ..liens])
        )

        (
            (let place_ty = env.place_ty(&place)?)
            (local_liens(&env, place_ty) => liens)
            ----------------------------------- ("leased")
            (local_liens_from_lien(_env, Lien::Leased(place)) => set![LocalLien::leased(&place), ..liens])
        )
    }
}

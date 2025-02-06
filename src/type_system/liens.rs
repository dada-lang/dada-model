use formality_core::{judgment_fn, set, Set};

use crate::{
    grammar::{NamedTy, Parameter},
    type_system::{
        env::Env,
        quantifiers::union,
        red_terms::{red_term, Chain, Lien, RedTerm, RedTy, TyChain},
    },
};

judgment_fn! {
    pub fn liens(
        env: Env,
        a: Parameter,
    ) => Set<Lien> {
        debug(a, env)

        (
            (red_term(&env, a) => red_term)
            (union(&red_term.ty_chains, &|ty_chain| liens_from_ty_chain(&env, ty_chain)) => liens)
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
            (union(ty_chains, &|ty_chain| liens_from_ty_chain(&env, ty_chain)) => liens)
            ----------------------------------- ("rule")
            (liens_from_red_term(env, RedTerm { ty_chains }) => liens)
        )
    }
}

judgment_fn! {
    fn liens_from_ty_chain(
        env: Env,
        a: TyChain,
    ) => Set<Lien> {
        debug(a, env)

        (
            (liens_from_red_ty(&env, ty) => liens_1)
            (liens_from_chain(&env, &chain) => liens_2)
            ----------------------------------- ("named")
            (liens_from_ty_chain(_env, TyChain { chain, ty }) => (&liens_1, liens_2))
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
judgment_fn! {
    fn liens_from_chain(
        env: Env,
        a: Chain,
    ) => Set<Lien> {
        debug(a, env)

        (
            ----------------------------------- ("none")
            (liens_from_chain(_env, Chain { liens }) => set![..liens])
        )
    }
}

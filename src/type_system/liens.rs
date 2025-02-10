use formality_core::{judgment_fn, set, Set};

use crate::{
    grammar::{NamedTy, Parameter},
    type_system::{
        env::Env,
        quantifiers::union,
        red_terms::{red_term, Chain, Lien, RedPerm, RedTerm, RedTy},
    },
};

judgment_fn! {
    pub fn liens(
        env: Env,
        a: Parameter,
    ) => Set<Lien> {
        debug(a, env)

        (
            (red_term(&env, a) => RedTerm { red_perm, red_ty })
            (liens_from_red_perm(&env, red_perm) => liens_1)
            (liens_from_red_ty(&env, &red_ty) => liens_2)
            ----------------------------------- ("my")
            (liens(env, a) => (&liens_1, liens_2))
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
    fn liens_from_red_perm(
        env: Env,
        a: RedPerm,
    ) => Set<Lien> {
        debug(a, env)

        (
            (union(chains, &|chain| liens_from_chain(&env, chain)) => liens)
            ----------------------------------- ("none")
            (liens_from_red_perm(_env, RedPerm { chains }) => liens)
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

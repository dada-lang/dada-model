use formality_core::{judgment_fn, Cons, Set};

use crate::{
    grammar::{NamedTy, Parameter, Perm, Place, Ty},
    type_system::{
        env::Env,
        liens::{lien_chains, ty_chains, Lien, LienChain, My, TyChain},
        places::place_ty,
    },
};

judgment_fn! {
    fn lien_set_from_chain(
        env: Env,
        a: LienChain,
    ) => (Env, Set<Lien>) {
        debug(a, env)

        (
            ----------------------------------- ("my")
            (lien_set_from_chain(env, My()) => (env, ()))
        )

        (
            (lien_set_from_chain(env, &chain) => (env, lien_set0))
            ----------------------------------- ("our")
            (lien_set_from_chain(env, Cons(Lien::Our, chain)) => (env, Cons(Lien::Our, lien_set0)))
        )

        (
            (lien_set_from_place(env, &place) => (env, lien_set0))
            (lien_set_from_chain(env, &chain) => (env, lien_set1))
            ----------------------------------- ("sh")
            (lien_set_from_chain(env, Cons(Lien::Shared(place), chain)) => (env, Cons(Lien::shared(&place), (&lien_set0, lien_set1))))
        )

        (
            (lien_set_from_place(env, &place) => (env, lien_set0))
            (lien_set_from_chain(env, &chain) => (env, lien_set1))
            ----------------------------------- ("l")
            (lien_set_from_chain(env, Cons(Lien::Leased(place), chain)) => (env, Cons(Lien::leased(&place), (&lien_set0, lien_set1))))
        )


        (
            (lien_set_from_chain(env, chain) => (env, lien_set0))
            ----------------------------------- ("var")
            (lien_set_from_chain(env, Cons(Lien::Var(var), chain)) => (env, Cons(Lien::Var(var), lien_set0)))
        )
    }
}

judgment_fn! {
    fn lien_set_from_place(
        env: Env,
        a: Place,
    ) => (Env, Set<Lien>) {
        debug(a, env)

        (
            (place_ty(&env, &place) => ty)
            (lien_set_from_parameter(&env, ty) => (env, lien_set))
            ----------------------------------- ("nil")
            (lien_set_from_place(env, place) => (env, lien_set))
        )

    }
}

judgment_fn! {
    pub fn lien_set_from_parameter(
        env: Env,
        a: Parameter,
    ) => (Env, Set<Lien>) {
        debug(a, env)

        (
            (ty_chains(env, My(), ty) => (env, ty_chains))
            (lien_set_from_ty_chains(env, ty_chains) => (env, lien_set))
            ----------------------------------- ("nil")
            (lien_set_from_parameter(env, ty: Ty) => (env, lien_set))
        )

        (
            (lien_chains(env, My(), perm) => (env, chains))
            (lien_set_from_chains(env, chains) => (env, lien_set))
            ----------------------------------- ("nil")
            (lien_set_from_parameter(env, perm: Perm) => (env, lien_set))
        )
    }
}

judgment_fn! {
    fn lien_set_from_parameters(
        env: Env,
        a: Vec<Parameter>,
    ) => (Env, Set<Lien>) {
        debug(a, env)

        (
            ----------------------------------- ("nil")
            (lien_set_from_parameters(env, ()) => (env, ()))
        )


        (
            (lien_set_from_parameter(env, p) => (env, lien_set0))
            (lien_set_from_parameters(env, &ps) => (env, lien_set1))
            ----------------------------------- ("cons")
            (lien_set_from_parameters(env, Cons(p, ps)) => (env, (&lien_set0, lien_set1)))
        )
    }
}

judgment_fn! {
    fn lien_set_from_ty_chains(
        env: Env,
        a: Set<TyChain>,
    ) => (Env, Set<Lien>) {
        debug(a, env)

        (
            ----------------------------------- ("nil")
            (lien_set_from_ty_chains(env, ()) => (env, ()))
        )

        (
            (lien_set_from_chain(env, liens) => (env, lien_set0))
            (lien_set_from_ty_chains(env, &liens1) => (env, lien_set1))
            ----------------------------------- ("nil")
            (lien_set_from_ty_chains(env, Cons(TyChain::Var(liens, _), liens1)) => (env, (&lien_set0, lien_set1)))
        )

        (
            (lien_set_from_chain(env, liens) => (env, lien_set0))
            (lien_set_from_ty_chains(env, &liens1) => (env, lien_set1))
            (lien_set_from_parameters(env, &parameters) => (env, lien_set2))
            ----------------------------------- ("nil")
            (lien_set_from_ty_chains(env, Cons(TyChain::NamedTy(liens, NamedTy { name: _, parameters }), liens1)) => (env, (&lien_set0, &lien_set1, lien_set2)))
        )
    }
}

judgment_fn! {
    fn lien_set_from_chains(
        env: Env,
        a: Set<LienChain>,
    ) => (Env, Set<Lien>) {
        debug(a, env)

        (
            ----------------------------------- ("nil")
            (lien_set_from_chains(env, ()) => (env, ()))
        )

        (
            (lien_set_from_chain(env, liens0) => (env, lien_set0))
            (lien_set_from_chains(env, &liens1) => (env, lien_set1))
            ----------------------------------- ("nil")
            (lien_set_from_chains(env, Cons(liens0, liens1)) => (env, (&lien_set0, lien_set1)))
        )
    }
}

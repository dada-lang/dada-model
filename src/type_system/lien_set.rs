use formality_core::{judgment_fn, Cons, Set};

use crate::{
    grammar::{NamedTy, Parameter, Perm, Place, Ty},
    type_system::{
        env::Env,
        lien_chains::{lien_chains, ty_chains, Lien, LienChain, My, TyChain},
        places::place_ty,
    },
};

judgment_fn! {
    fn lien_set_from_chain(
        env: Env,
        a: LienChain,
    ) => Set<Lien> {
        debug(a, env)

        (
            ----------------------------------- ("my")
            (lien_set_from_chain(_env, My()) => ())
        )

        (
            (lien_set_from_chain(env, &chain) => lien_set0)
            ----------------------------------- ("our")
            (lien_set_from_chain(env, Cons(Lien::Our, chain)) => Cons(Lien::Our, lien_set0))
        )

        (
            (lien_set_from_place(&env, &place) => lien_set0)
            (lien_set_from_chain(&env, &chain) => lien_set1)
            ----------------------------------- ("sh")
            (lien_set_from_chain(env, Cons(Lien::Shared(place), chain)) => Cons(Lien::shared(&place), (&lien_set0, lien_set1)))
        )

        (
            (lien_set_from_place(&env, &place) => lien_set0)
            (lien_set_from_chain(&env, &chain) => lien_set1)
            ----------------------------------- ("l")
            (lien_set_from_chain(env, Cons(Lien::Leased(place), chain)) => Cons(Lien::leased(&place), (&lien_set0, lien_set1)))
        )


        (
            (lien_set_from_chain(env, chain) => lien_set0)
            ----------------------------------- ("var")
            (lien_set_from_chain(env, Cons(Lien::Var(var), chain)) => Cons(Lien::Var(var), lien_set0))
        )
    }
}

judgment_fn! {
    fn lien_set_from_place(
        env: Env,
        a: Place,
    ) => Set<Lien> {
        debug(a, env)

        (
            (place_ty(&env, &place) => ty)
            (lien_set_from_parameter(&env, ty) => lien_set)
            ----------------------------------- ("nil")
            (lien_set_from_place(env, place) => lien_set)
        )

    }
}

judgment_fn! {
    pub fn lien_set_from_parameter(
        env: Env,
        a: Parameter,
    ) => Set<Lien> {
        debug(a, env)

        (
            (ty_chains(&env, My(), ty) => ty_chains)
            (lien_set_from_ty_chains(&env, ty_chains) => lien_set)
            ----------------------------------- ("nil")
            (lien_set_from_parameter(env, ty: Ty) => lien_set)
        )

        (
            (lien_chains(&env, My(), perm) => chains)
            (lien_set_from_chains(&env, chains) => lien_set)
            ----------------------------------- ("nil")
            (lien_set_from_parameter(env, perm: Perm) => lien_set)
        )
    }
}

judgment_fn! {
    fn lien_set_from_parameters(
        env: Env,
        a: Vec<Parameter>,
    ) => Set<Lien> {
        debug(a, env)

        (
            ----------------------------------- ("nil")
            (lien_set_from_parameters(_env, ()) => ())
        )


        (
            (lien_set_from_parameter(&env, p) => lien_set0)
            (lien_set_from_parameters(&env, &ps) => lien_set1)
            ----------------------------------- ("cons")
            (lien_set_from_parameters(env, Cons(p, ps)) => (&lien_set0, lien_set1))
        )
    }
}

judgment_fn! {
    fn lien_set_from_ty_chains(
        env: Env,
        a: Set<TyChain>,
    ) => Set<Lien> {
        debug(a, env)

        (
            ----------------------------------- ("nil")
            (lien_set_from_ty_chains(_env, ()) => ())
        )

        (
            (lien_set_from_chain(&env, liens) => lien_set0)
            (lien_set_from_ty_chains(&env, &liens1) => lien_set1)
            ----------------------------------- ("nil")
            (lien_set_from_ty_chains(env, Cons(TyChain::Var(liens, _), liens1)) => (&lien_set0, lien_set1))
        )

        (
            (lien_set_from_chain(&env, liens) => lien_set0)
            (lien_set_from_ty_chains(&env, &liens1) => lien_set1)
            (lien_set_from_parameters(&env, &parameters) => lien_set2)
            ----------------------------------- ("nil")
            (lien_set_from_ty_chains(env, Cons(TyChain::NamedTy(liens, NamedTy { name: _, parameters }), liens1)) => (&lien_set0, &lien_set1, lien_set2))
        )
    }
}

judgment_fn! {
    fn lien_set_from_chains(
        env: Env,
        a: Set<LienChain>,
    ) => Set<Lien> {
        debug(a, env)

        (
            ----------------------------------- ("nil")
            (lien_set_from_chains(_env, ()) => ())
        )

        (
            (lien_set_from_chain(&env, liens0) => lien_set0)
            (lien_set_from_chains(&env, &liens1) => lien_set1)
            ----------------------------------- ("nil")
            (lien_set_from_chains(env, Cons(liens0, liens1)) => (&lien_set0, lien_set1))
        )
    }
}

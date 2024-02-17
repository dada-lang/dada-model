use formality_core::{judgment_fn, Cons};

use crate::{
    grammar::{Parameter, Predicate},
    type_system::{
        env::Env,
        lien_chains::{lien_chains, Lien, LienChain, My},
        predicates::prove_predicate,
        quantifiers::for_all,
    },
};

judgment_fn! {
    /// A parameter `a` is **shared** when it represents shared access to
    /// the original object (specifically, the lack of unique access).
    /// Note that owned types are subtypes of shared types,
    /// but they are not *shared*, because they have unique access
    pub fn is_shared(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (lien_chains(&env, My(), a) => chains)
            (for_all(chains, &|chain| lien_chain_is_shared(&env, chain)) => ())
            ---------------------- ("is_shared")
            (is_shared(env, a) => ())
        )
    }
}

judgment_fn! {
    /// A parameter `a` is **leased** when it definitively represents leased access to
    /// the original object.
    pub fn is_leased(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (lien_chains(&env, My(), a) => chains)
            (for_all(chains, &|chain| lien_chain_is_leased(&env, chain)) => ())
            ---------------------- ("is_leased")
            (is_leased(env, a) => ())
        )
    }
}

judgment_fn! {
    /// A parameter `a` is **leased** when it definitively represents leased access to
    /// the original object.
    pub fn is_unique(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (lien_chains(&env, My(), a) => chains)
            (for_all(chains, &|chain| lien_chain_is_unique(&env, chain)) => ())
            ---------------------- ("is_leased")
            (is_unique(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn lien_chain_is_shared(
        env: Env,
        chain: LienChain,
    ) => () {
        debug(chain, env)

        (
            -------------------------- ("our")
            (lien_chain_is_shared(_env, Cons(Lien::Our, _)) => ())
        )

        (
            -------------------------- ("shared")
            (lien_chain_is_shared(_env, Cons(Lien::Shared(_), _)) => ())
        )

        (
            (prove_predicate(env, Predicate::shared(v)) => ())
            -------------------------- ("var")
            (lien_chain_is_shared(env, Cons(Lien::Var(v), _)) => ())
        )
    }
}

judgment_fn! {
    pub fn lien_chain_is_leased(
        env: Env,
        chain: LienChain,
    ) => () {
        debug(chain, env)

        (
            -------------------------- ("leased")
            (lien_chain_is_leased(_env, Cons(Lien::Leased(_), _)) => ())
        )

        (
            (prove_predicate(env, Predicate::leased(v)) => ())
            -------------------------- ("var")
            (lien_chain_is_leased(env, Cons(Lien::Var(v), _)) => ())
        )
    }
}

judgment_fn! {
    pub fn lien_chain_is_unique(
        env: Env,
        chain: LienChain,
    ) => () {
        debug(chain, env)

        (
            -------------------------- ("my")
            (lien_chain_is_unique(_env, My()) => ())
        )

        (
            (lien_chain_is_leased(env, chain) => ())
            -------------------------- ("leased")
            (lien_chain_is_unique(env, chain) => ())
        )
    }
}

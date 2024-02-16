use formality_core::{judgment_fn, Cons};

use crate::{
    grammar::{Parameter, Predicate},
    type_system::{
        env::Env,
        lien_chains::{lien_chains, Lien, LienChain, My},
        predicates::prove_predicate,
        quantifiers::fold,
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
    ) => Env {
        debug(a, env)

        (
            (lien_chains(&env, My(), a) => (env, chains))
            (fold(env, chains, &|env, chain| {
                lien_chain_is_shared(&env, chain)
            }) => env)
             ---------------------- ("is_shared")
            (is_shared(env, a) => env)
        )
    }
}

judgment_fn! {
    /// A parameter `a` is **leased** when it definitively represents leased access to
    /// the original object.
    pub fn is_leased(
        env: Env,
        a: Parameter,
    ) => Env {
        debug(a, env)

        (
            (lien_chains(&env, My(), a) => (env, chains))
            (fold(env, chains, &|env, chain| {
                lien_chain_is_leased(&env, chain)
            }) => env)
            ---------------------- ("is_leased")
            (is_leased(env, a) => env)
        )
    }
}

judgment_fn! {
    /// A parameter `a` is **leased** when it definitively represents leased access to
    /// the original object.
    pub fn is_unique(
        env: Env,
        a: Parameter,
    ) => Env {
        debug(a, env)

        (
            (lien_chains(&env, My(), a) => (env, chains))
            (fold(env, chains, &|env, chain| {
                lien_chain_is_unique(&env, chain)
            }) => env)
            ---------------------- ("is_leased")
            (is_unique(env, a) => env)
        )
    }
}

judgment_fn! {
    fn lien_chain_is_shared(
        env: Env,
        chain: LienChain,
    ) => Env {
        debug(chain, env)

        (
            -------------------------- ("our")
            (lien_chain_is_shared(env, Cons(Lien::Our, _)) => env)
        )

        (
            -------------------------- ("shared")
            (lien_chain_is_shared(env, Cons(Lien::Shared(_), _)) => env)
        )

        (
            (prove_predicate(env, Predicate::shared(v)) => env)
            -------------------------- ("var")
            (lien_chain_is_shared(env, Cons(Lien::Var(v), _)) => env)
        )
    }
}

judgment_fn! {
    fn lien_chain_is_leased(
        env: Env,
        chain: LienChain,
    ) => Env {
        debug(chain, env)

        (
            -------------------------- ("leased")
            (lien_chain_is_leased(env, Cons(Lien::Leased(_), _)) => env)
        )

        (
            (prove_predicate(env, Predicate::leased(v)) => env)
            -------------------------- ("var")
            (lien_chain_is_leased(env, Cons(Lien::Var(v), _)) => env)
        )
    }
}

judgment_fn! {
    fn lien_chain_is_unique(
        env: Env,
        chain: LienChain,
    ) => Env {
        debug(chain, env)

        (
            -------------------------- ("my")
            (lien_chain_is_unique(env, My()) => env)
        )

        (
            (lien_chain_is_leased(env, chain) => env)
            -------------------------- ("leased")
            (lien_chain_is_unique(env, chain) => env)
        )
    }
}

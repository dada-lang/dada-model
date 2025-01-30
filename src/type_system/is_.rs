use formality_core::{judgment_fn, Cons};

use crate::{
    grammar::{Parameter, Predicate},
    type_system::{
        env::Env,
        lien2::liens,
        lien_chains::{lien_chains, Lien, LienChain, My, Our},
        predicates::prove_predicate,
        quantifiers::for_all,
    },
};

judgment_fn! {
    /// A parameter `a` is **copy** when a value of this type, or of a type
    /// with this permission, is non-affine and hence is copied upon being
    /// given rather than moved.
    ///
    /// Note that "copy" does not respect Liskov Substitution Principle:
    /// `my` is not `copy` but is a subtype of `our` which *is* copy.
    pub fn is_copy(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (lien_chains(&env, My(), a) => chains)
            (for_all(chains, &|chain| lien_chain_is_copy(&env, chain)) => ())
            ---------------------- ("is_copy")
            (is_copy(env, a) => ())
        )
    }
}

judgment_fn! {
    /// A parameter `a` is **copy** when a value of this type, or of a type
    /// with this permission, is non-affine and hence is copied upon being
    /// given rather than moved.
    ///
    /// Note that "copy" does not respect Liskov Substitution Principle:
    /// `my` is not `copy` but is a subtype of `our` which *is* copy.
    pub fn is_lent(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (liens(&env, a) => liens_a)
            (if liens_a.is_lent(&env))
            ---------------------- ("is_lent")
            (is_lent(env, a) => ())
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
    pub fn lien_chain_is_copy(
        env: Env,
        chain: LienChain,
    ) => () {
        debug(chain, env)

        (
            -------------------------- ("our")
            (lien_chain_is_copy(_env, Cons(Lien::Our, _)) => ())
        )

        (
            -------------------------- ("shared")
            (lien_chain_is_copy(_env, Cons(Lien::Shared(_), _)) => ())
        )

        (
            (prove_predicate(env, Predicate::copy(v)) => ())
            -------------------------- ("var")
            (lien_chain_is_copy(env, Cons(Lien::Var(v), _)) => ())
        )
    }
}

judgment_fn! {
    pub fn lien_chain_is_owned(
        env: Env,
        chain: LienChain,
    ) => () {
        debug(chain, env)

        (
            -------------------------- ("our")
            (lien_chain_is_owned(_env, Our()) => ())
        )


        (
            -------------------------- ("my")
            (lien_chain_is_owned(_env, My()) => ())
        )

        (
            (prove_predicate(&env, Predicate::owned(v)) => ())
            (lien_chain_is_owned(&env, &chain) => ())
            -------------------------- ("var")
            (lien_chain_is_owned(env, Cons(Lien::Var(v), chain)) => ())
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

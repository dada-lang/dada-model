use formality_core::judgment_fn;

use crate::{
    dada_lang::grammar::UniversalVar,
    grammar::{Parameter, Predicate},
    type_system::{env::Env, terms},
};

judgment_fn! {
    /// A parameter `a` is **shared** when it represents shared access to
    /// the original object (specifically, the lack of unique access).
    /// Note that owned types are subtypes of shared types,
    /// but they are not *shared*, because they have unique access
    pub fn is_shared_var(
        env: Env,
        a: UniversalVar,
    ) => Env {
        debug(a, env)

        (
            (if env.contains_assumption(Predicate::shared(v)))
            ---------------------- ("universal")
            (is_shared_var(env, v) => env)
        )
    }
}

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
            (terms::terms(env, v) => (env, terms))
            (if !terms.unique)
            (if terms.shared)
            ---------------------- ("is_shared")
            (is_shared(env, v) => env)
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
            (terms::terms(env, a) => (env, terms))
            (if terms.leased)
            (if !terms.shared)
            ---------------------- ("is_leased")
            (is_leased(env, a) => env)
        )
    }
}

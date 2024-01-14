use super::{env::Env, types::check_parameter};
use crate::{
    dada_lang::grammar::UniversalVar,
    grammar::{Parameter, Predicate},
    type_system::{
        quantifiers::fold,
        subtypes::{is_leased, is_mine, is_shared},
    },
};
use anyhow::bail;
use fn_error_context::context;
use formality_core::{judgment_fn, Downcast, Fallible};

#[context("check predicates `{:?}`", predicates)]
pub fn check_predicates(env: &Env, predicates: &[Predicate]) -> Fallible<()> {
    for predicate in predicates {
        check_predicate(env, predicate)?;
    }
    Ok(())
}

#[context("check predicate `{:?}`", predicate)]
pub fn check_predicate(env: &Env, predicate: &Predicate) -> Fallible<()> {
    match predicate {
        Predicate::Shared(parameter)
        | Predicate::Leased(parameter)
        | Predicate::Mine(parameter) => check_predicate_parameter(env, parameter),
    }
}

#[context("check check_predicate_parameter `{:?}`", parameter)]
pub fn check_predicate_parameter(env: &Env, parameter: &Parameter) -> Fallible<()> {
    check_parameter(env, parameter)?;

    if let None = parameter.downcast::<UniversalVar>() {
        bail!("predicates must be applied to generic parameters")
    }

    Ok(())
}

judgment_fn! {
    pub fn prove_predicates(
        env: Env,
        predicate: Vec<Predicate>,
    ) => Env {
        debug(predicate, env)

        (
            (fold(env, predicates, &|env, predicate| {
                prove_predicate(env, predicate)
            }) => env)
            ----------------------- ("prove_predicates")
            (prove_predicates(env, predicates) => env)
        )
    }
}

judgment_fn! {
    pub fn prove_predicate(
        env: Env,
        predicate: Predicate,
    ) => Env {
        debug(predicate, env)

        (
            (env.assumptions() => assumption)
            (if *assumption == predicate)!
            ---------------------------- ("assumption")
            (prove_predicate(env, predicate) => &env)
        )

        (
            (is_shared(env, p) => env)
            ---------------------------- ("shared")
            (prove_predicate(env, Predicate::Shared(p)) => env)
        )

        (
            (is_leased(env, p) => env)
            ---------------------------- ("leased")
            (prove_predicate(env, Predicate::Leased(p)) => env)
        )

        (
            (is_mine(env, p) => env)
            ---------------------------- ("mine")
            (prove_predicate(env, Predicate::Mine(p)) => env)
        )
    }
}

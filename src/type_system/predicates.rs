use super::{env::Env, types::check_parameter};
use crate::{
    dada_lang::grammar::UniversalVar,
    grammar::{Parameter, Predicate, PredicateKind},
    type_system::{
        is_::{is_leased, is_shared},
        quantifiers::for_all,
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
    let Predicate { kind: _, parameter } = predicate;
    check_predicate_parameter(env, parameter)
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
    ) => () {
        debug(predicate, env)

        (
            (for_all(predicates, &|predicate| prove_predicate(&env, predicate)) => ())
            ----------------------- ("prove_predicates")
            (prove_predicates(env, predicates) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_predicate(
        env: Env,
        predicate: Predicate,
    ) => () {
        debug(predicate, env)

        (
            (env.assumptions() => assumption)
            (if *assumption == predicate)!
            ---------------------------- ("assumption")
            (prove_predicate(env, predicate) => ())
        )

        (
            (is_shared(env, p) => ())
            ---------------------------- ("shared")
            (prove_predicate(env, Predicate { kind: PredicateKind::Shared, parameter: p }) => ())
        )

        (
            (is_leased(env, p) => ())
            ---------------------------- ("leased")
            (prove_predicate(env, Predicate { kind: PredicateKind::Leased, parameter: p }) => ())
        )
    }
}

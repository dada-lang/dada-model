use super::{env::Env, types::check_parameter};
use crate::{
    dada_lang::grammar::UniversalVar,
    grammar::{NamedTy, Parameter, Perm, Place, Predicate, Ty, VarianceKind},
    type_system::quantifiers::for_all,
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
        Predicate::Copy(parameter) => check_predicate_parameter(env, parameter),
        Predicate::Variance(_kind, parameter) => check_predicate_parameter(env, parameter),
        Predicate::Moved(parameter) => check_predicate_parameter(env, parameter),
        Predicate::Owned(parameter) => check_predicate_parameter(env, parameter),
        Predicate::Lent(parameter) => check_predicate_parameter(env, parameter),
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
    pub fn prove_is_copy(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_predicate(env, Predicate::Copy(a)) => ())
            ---------------------------- ("is-copy")
            (prove_is_copy(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_is_moved(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_predicate(env, Predicate::Moved(a)) => ())
            ---------------------------- ("is-moved")
            (prove_is_moved(env, a) => ())
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
            (let is_copy = env.is_copy(&p)?)
            (if is_copy)
            ---------------------------- ("shared")
            (prove_predicate(env, Predicate::Copy(p)) => ())
        )

        (
            (let is_moved = env.is_moved(&p)?)
            (if is_moved)
            ---------------------------- ("moved")
            (prove_predicate(env, Predicate::Moved(p)) => ())
        )

        (
            (variance_predicate(env, kind, parameter) => ())
            ---------------------------- ("variance")
            (prove_predicate(env, Predicate::Variance(kind, parameter)) => ())
        )
    }
}

judgment_fn! {
    fn variance_predicate(
        env: Env,
        kind: VarianceKind,
        parameter: Parameter,
    ) => () {
        debug(kind, parameter, env)

        (
            (for_all(parameters, &|parameter| prove_predicate(&env, kind.apply(parameter))) => ())
            ----------------------------- ("ty-named")
            (variance_predicate(env, kind, NamedTy { name: _, parameters }) => ())
        )

        (
            (prove_predicate(&env, kind.apply(&*ty1)) => ())
            (prove_predicate(&env, kind.apply(&*ty2)) => ())
            ----------------------------- ("ty-or")
            (variance_predicate(env, kind, Ty::Or(ty1, ty2)) => ())
        )

        (
            (prove_predicate(&env, kind.apply(perm)) => ())
            (prove_predicate(&env, kind.apply(&*ty)) => ())
            ----------------------------- ("ty")
            (variance_predicate(env, kind, Ty::ApplyPerm(perm, ty)) => ())
        )

        (
            ----------------------------- ("my")
            (variance_predicate(_env, _kind, Perm::My) => ())
        )

        (
            ----------------------------- ("our")
            (variance_predicate(_env, _kind, Perm::Our) => ())
        )

        // FIXME: Is this right? What about e.g. `struct Foo[perm P, ty T] { x: T, y: P shared[x] String }`
        // or other such things? and what about `given[x]`?

        (
            ----------------------------- ("shared")
            (variance_predicate(_env, _kind, Perm::Shared(_)) => ())
        )

        (
            (for_all(places, &|place| variance_predicate_place(&env, kind, place)) => ())
            ----------------------------- ("leased")
            (variance_predicate(env, kind, Perm::Leased(places)) => ())
        )

        (
            (for_all(places, &|place| variance_predicate_place(&env, kind, place)) => ())
            ----------------------------- ("given")
            (variance_predicate(env, kind, Perm::Given(places)) => ())
        )

        (
            (prove_predicate(&env, kind.apply(&*perm1)) => ())
            (prove_predicate(&env, kind.apply(&*perm2)) => ())
            ----------------------------- ("perm-or")
            (variance_predicate(env, kind, Perm::Or(perm1, perm2)) => ())
        )

        (
            (prove_predicate(&env, kind.apply(&*perm1)) => ())
            (prove_predicate(&env, kind.apply(&*perm2)) => ())
            ----------------------------- ("perm-apply")
            (variance_predicate(env, kind, Perm::Apply(perm1, perm2)) => ())
        )

    }
}

judgment_fn! {
    fn variance_predicate_place(
        env: Env,
        kind: VarianceKind,
        place: Place,
    ) => () {
        debug(kind, place, env)

        (
            (let ty = env.place_ty(&place)?)
            (prove_predicate(&env, kind.apply(ty)) => ())
            ----------------------------- ("perm")
            (variance_predicate_place(env, kind, place) => ())
        )
    }
}

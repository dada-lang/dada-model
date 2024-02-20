use super::{env::Env, types::check_parameter};
use crate::{
    dada_lang::grammar::UniversalVar,
    grammar::{NamedTy, Parameter, Perm, Place, Predicate, PredicateKind, Ty},
    type_system::{
        is_::{is_leased, is_shared},
        places::place_ty,
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

        (
            (variance_predicate(env, PredicateKind::Relative, parameter) => ())
            ---------------------------- ("relative")
            (prove_predicate(env, Predicate { kind: PredicateKind::Relative, parameter }) => ())
        )

        (
            (variance_predicate(env, PredicateKind::Atomic, parameter) => ())
            ---------------------------- ("atomic")
            (prove_predicate(env, Predicate { kind: PredicateKind::Atomic, parameter }) => ())
        )
    }
}

judgment_fn! {
    fn variance_predicate(
        env: Env,
        kind: PredicateKind,
        parameter: Parameter,
    ) => () {
        debug(kind, parameter, env)

        (
            (for_all(parameters, &|parameter| prove_predicate(&env, Predicate::new(kind, parameter))) => ())
            ----------------------------- ("ty-named")
            (variance_predicate(env, kind, NamedTy { name: _, parameters }) => ())
        )

        (
            (prove_predicate(&env, Predicate::new(kind, &*ty1)) => ())
            (prove_predicate(&env, Predicate::new(kind, &*ty2)) => ())
            ----------------------------- ("ty-or")
            (variance_predicate(env, kind, Ty::Or(ty1, ty2)) => ())
        )

        (
            (prove_predicate(&env, Predicate::new(kind, perm)) => ())
            (prove_predicate(&env, Predicate::new(kind, &*ty)) => ())
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

        // FIXME: Is this right? What about e.g. `struct Foo[perm P, ty T] { x: T, y: P shared{x} String }`
        // or other such things? and what about `given{x}`?

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
            (prove_predicate(&env, Predicate::new(kind, &*perm1)) => ())
            (prove_predicate(&env, Predicate::new(kind, &*perm2)) => ())
            ----------------------------- ("perm-or")
            (variance_predicate(env, kind, Perm::Or(perm1, perm2)) => ())
        )

        (
            (prove_predicate(&env, Predicate::new(kind, &*perm1)) => ())
            (prove_predicate(&env, Predicate::new(kind, &*perm2)) => ())
            ----------------------------- ("perm-apply")
            (variance_predicate(env, kind, Perm::Apply(perm1, perm2)) => ())
        )

    }
}

judgment_fn! {
    fn variance_predicate_place(
        env: Env,
        kind: PredicateKind,
        place: Place,
    ) => () {
        debug(kind, place, env)

        (
            (place_ty(&env, place) => ty)
            (prove_predicate(&env, Predicate::new(kind, ty)) => ())
            ----------------------------- ("perm")
            (variance_predicate_place(env, kind, place) => ())
        )
    }
}

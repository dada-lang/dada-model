use std::sync::Arc;

use super::{env::Env, types::check_parameter};
use crate::{
    dada_lang::grammar::UniversalVar,
    grammar::{
        NamedTy, Parameter, ParameterPredicate, Perm, Place, Predicate, Ty, Variable, VarianceKind,
    },
    type_system::quantifiers::for_all,
};
use anyhow::bail;
use fn_error_context::context;
use formality_core::{judgment_fn, Downcast, Fallible, ProvenSet, Upcast};

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
        Predicate::Parameter(_kind, parameter) => check_predicate_parameter(env, parameter),
        Predicate::Variance(_kind, parameter) => check_predicate_parameter(env, parameter),
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
            (prove_predicate(env, Predicate::copy(a)) => ())
            ---------------------------- ("is-copy")
            (prove_is_copy(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_is_move(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_predicate(env, Predicate::move_(a)) => ())
            ---------------------------- ("is-moved")
            (prove_is_move(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_is_lent(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_predicate(env, Predicate::lent(a)) => ())
            ---------------------------- ("is-lent")
            (prove_is_lent(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_is_owned(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_predicate(env, Predicate::owned(a)) => ())
            ---------------------------- ("is-owned")
            (prove_is_owned(env, a) => ())
        )
    }
}

pub fn prove_is_move_if_some(
    env: impl Upcast<Env>,
    a: impl Upcast<Option<Parameter>>,
) -> ProvenSet<()> {
    let a: Option<Parameter> = a.upcast();
    match a {
        Some(a) => prove_is_move(env, a),
        None => ProvenSet::singleton(()),
    }
}

// FIXME: Why does the judgment function below not work but the function above does?
// judgment_fn! {
//     pub fn prove_is_move_if_some(
//         env: Env,
//         a: Option<Parameter>,
//     ) => () {
//         debug(a, env)

//         (
//             (prove_predicate(env, Predicate::move_(a)) => ())
//             ---------------------------- ("is-move-some")
//             (prove_is_move_if_some(env, Some::<Parameter>(a)) => ()) // annoying type hint that doesn't seem like it should be needed
//         )

//         (
//             ---------------------------- ("is-move-none")
//             (prove_is_move_if_some(_env, Option::<Parameter>::None) => ())
//         )
//     }
// }

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
            (if let true = p.meets_predicate(&env, k)?)
            ---------------------------- ("parameter")
            (prove_predicate(env, Predicate::Parameter(k, p)) => ())
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

pub trait MeetsPredicate {
    fn is_copy(&self, env: &Env) -> Fallible<bool> {
        self.meets_predicate(env, ParameterPredicate::Copy)
    }

    fn meets_predicate(&self, env: &Env, predicate: ParameterPredicate) -> Fallible<bool>;
}

impl<S> MeetsPredicate for &S
where
    S: MeetsPredicate,
{
    fn meets_predicate(&self, env: &Env, predicate: ParameterPredicate) -> Fallible<bool> {
        S::meets_predicate(self, env, predicate)
    }
}

impl<S> MeetsPredicate for Arc<S>
where
    S: MeetsPredicate,
{
    fn meets_predicate(&self, env: &Env, predicate: ParameterPredicate) -> Fallible<bool> {
        S::meets_predicate(self, env, predicate)
    }
}

struct Many<I>(I);

impl<I> MeetsPredicate for Many<I>
where
    I: IntoIterator<Item: MeetsPredicate> + Clone,
{
    fn meets_predicate(&self, env: &Env, predicate: ParameterPredicate) -> Fallible<bool> {
        match predicate {
            ParameterPredicate::Copy | ParameterPredicate::Lent => {
                Any(self.0.clone()).meets_predicate(env, predicate)
            }
            ParameterPredicate::Move_ | ParameterPredicate::Owned => {
                All(self.0.clone()).meets_predicate(env, predicate)
            }
        }
    }
}

struct Any<I>(I);

impl<I> MeetsPredicate for Any<I>
where
    I: IntoIterator<Item: MeetsPredicate> + Clone,
{
    fn meets_predicate(&self, env: &Env, predicate: ParameterPredicate) -> Fallible<bool> {
        for item in self.0.clone() {
            if item.meets_predicate(env, predicate)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
}

struct All<I>(I);

impl<I> MeetsPredicate for All<I>
where
    I: IntoIterator<Item: MeetsPredicate> + Clone,
{
    fn meets_predicate(&self, env: &Env, predicate: ParameterPredicate) -> Fallible<bool> {
        for item in self.0.clone() {
            if !item.meets_predicate(env, predicate)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

impl MeetsPredicate for Place {
    fn meets_predicate(&self, env: &Env, predicate: ParameterPredicate) -> Fallible<bool> {
        let place_ty = env.place_ty(self)?;
        place_ty.meets_predicate(env, predicate)
    }
}

impl MeetsPredicate for Parameter {
    fn meets_predicate(&self, env: &Env, predicate: ParameterPredicate) -> Fallible<bool> {
        match self {
            Parameter::Ty(ty) => ty.meets_predicate(env, predicate),
            Parameter::Perm(perm) => perm.meets_predicate(env, predicate),
        }
    }
}

impl MeetsPredicate for Ty {
    fn meets_predicate(&self, env: &Env, predicate: ParameterPredicate) -> Fallible<bool> {
        match self {
            Ty::NamedTy(named_ty) => named_ty.meets_predicate(env, predicate),
            Ty::Var(Variable::UniversalVar(v)) => v.meets_predicate(env, predicate),
            Ty::Var(Variable::ExistentialVar(_)) | Ty::Var(Variable::BoundVar(_)) => {
                panic!("unexpected variable: {self:?}")
            }
            Ty::ApplyPerm(perm, ty) => Compose(perm, ty).meets_predicate(env, predicate),
        }
    }
}

impl MeetsPredicate for NamedTy {
    fn meets_predicate(&self, env: &Env, k: ParameterPredicate) -> Fallible<bool> {
        let NamedTy { name, parameters } = self;
        if env.is_value_ty(name) {
            // Value types are copy iff all of their parameters are copy.
            match k {
                ParameterPredicate::Copy => {
                    All(parameters).meets_predicate(env, ParameterPredicate::Copy)
                }
                ParameterPredicate::Move_ => {
                    Any(parameters).meets_predicate(env, ParameterPredicate::Move_)
                }
                ParameterPredicate::Owned => {
                    All(parameters).meets_predicate(env, ParameterPredicate::Owned)
                }
                ParameterPredicate::Lent => Ok(false),
            }
        } else {
            // Classes are always move.
            match k {
                ParameterPredicate::Copy => Ok(false),
                ParameterPredicate::Move_ => Ok(true),
                ParameterPredicate::Owned => {
                    All(parameters).meets_predicate(env, ParameterPredicate::Owned)
                }
                ParameterPredicate::Lent => Ok(false),
            }
        }
    }
}

impl MeetsPredicate for Perm {
    fn meets_predicate(&self, env: &Env, k: ParameterPredicate) -> Fallible<bool> {
        match self {
            crate::grammar::Perm::My => match k {
                ParameterPredicate::Move_ | ParameterPredicate::Owned => Ok(true),
                ParameterPredicate::Copy | ParameterPredicate::Lent => Ok(false),
            },
            crate::grammar::Perm::Our => match k {
                ParameterPredicate::Copy | ParameterPredicate::Owned => Ok(true),
                ParameterPredicate::Move_ | ParameterPredicate::Lent => Ok(false),
            },
            crate::grammar::Perm::Given(places) => Many(places).meets_predicate(env, k),
            crate::grammar::Perm::Shared(places) => {
                Many(places.iter().map(|place| SharedFrom(place))).meets_predicate(env, k)
            }
            crate::grammar::Perm::Leased(places) => {
                Many(places.iter().map(|place| LeasedFrom(place))).meets_predicate(env, k)
            }
            crate::grammar::Perm::Var(Variable::UniversalVar(v)) => v.meets_predicate(env, k),
            crate::grammar::Perm::Var(Variable::ExistentialVar(_))
            | crate::grammar::Perm::Var(Variable::BoundVar(_)) => {
                panic!("unexpected variable: {self:?}")
            }
            crate::grammar::Perm::Apply(perm, perm1) => {
                Compose(perm, perm1).meets_predicate(env, k)
            }
        }
    }
}

impl MeetsPredicate for UniversalVar {
    fn meets_predicate(&self, env: &Env, k: ParameterPredicate) -> Fallible<bool> {
        Ok(env.assumed_to_meet(self, k))
    }
}

struct Compose<S1, S2>(S1, S2);

impl<S1, S2> MeetsPredicate for Compose<S1, S2>
where
    S1: MeetsPredicate,
    S2: MeetsPredicate,
{
    fn meets_predicate(&self, env: &Env, k: ParameterPredicate) -> Fallible<bool> {
        let Compose(lhs, rhs) = self;

        if rhs.meets_predicate(env, ParameterPredicate::Copy)? {
            // In this case, `(perm ty) = ty`, so just check for `ty`
            rhs.meets_predicate(env, k)
        } else {
            match k {
                ParameterPredicate::Copy | ParameterPredicate::Lent => {
                    Ok(lhs.meets_predicate(env, k)? || rhs.meets_predicate(env, k)?)
                }
                ParameterPredicate::Move_ | ParameterPredicate::Owned => {
                    Ok(lhs.meets_predicate(env, k)? && rhs.meets_predicate(env, k)?)
                }
            }
        }
    }
}

/// The "essence" of leased-ness, this "subject" is composed with the
/// leased place `p` to figure out the permission of `leased[p]`.
struct SomeShared;

impl MeetsPredicate for SomeShared {
    fn meets_predicate(&self, _env: &Env, k: ParameterPredicate) -> Fallible<bool> {
        match k {
            ParameterPredicate::Copy | ParameterPredicate::Lent => Ok(true),
            ParameterPredicate::Move_ | ParameterPredicate::Owned => Ok(false),
        }
    }
}

struct SharedFrom<S>(S);

impl<S: MeetsPredicate> MeetsPredicate for SharedFrom<S> {
    fn meets_predicate(&self, env: &Env, k: ParameterPredicate) -> Fallible<bool> {
        Compose(SomeShared, &self.0).meets_predicate(env, k)
    }
}

/// The "essence" of leased-ness, this "subject" is composed with the
/// leased place `p` to figure out the permission of `leased[p]`.
struct SomeLeased;

impl MeetsPredicate for SomeLeased {
    fn meets_predicate(&self, _env: &Env, k: ParameterPredicate) -> Fallible<bool> {
        match k {
            ParameterPredicate::Lent | ParameterPredicate::Move_ => Ok(true),
            ParameterPredicate::Owned | ParameterPredicate::Copy => Ok(false),
        }
    }
}

struct LeasedFrom<S>(S);

impl<S: MeetsPredicate> MeetsPredicate for LeasedFrom<S> {
    fn meets_predicate(&self, env: &Env, k: ParameterPredicate) -> Fallible<bool> {
        Compose(SomeLeased, &self.0).meets_predicate(env, k)
    }
}

#[expect(dead_code)] // seems like it might be useful later
trait Adjective {
    fn subject_is(&self, env: &Env, subject: &impl MeetsPredicate) -> Fallible<bool>;
}

impl Adjective for ParameterPredicate {
    fn subject_is(&self, env: &Env, subject: &impl MeetsPredicate) -> Fallible<bool> {
        subject.meets_predicate(env, *self)
    }
}

#[expect(dead_code)] // seems like it might be useful later
struct Or<P1, P2>(P1, P2);

impl<P1, P2> Adjective for Or<P1, P2>
where
    P1: Adjective,
    P2: Adjective,
{
    fn subject_is(&self, env: &Env, subject: &impl MeetsPredicate) -> Fallible<bool> {
        Ok(self.0.subject_is(env, subject)? || self.1.subject_is(env, subject)?)
    }
}

#[expect(dead_code)] // seems like it might be useful later
struct And<P1, P2>(P1, P2);

impl<P1, P2> Adjective for And<P1, P2>
where
    P1: Adjective,
    P2: Adjective,
{
    fn subject_is(&self, env: &Env, subject: &impl MeetsPredicate) -> Fallible<bool> {
        Ok(self.0.subject_is(env, subject)? && self.1.subject_is(env, subject)?)
    }
}

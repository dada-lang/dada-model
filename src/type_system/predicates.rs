use std::sync::Arc;

use super::{env::Env, types::check_parameter};
use crate::{
    dada_lang::grammar::UniversalVar,
    grammar::{
        ClassPredicate, NamedTy, Parameter, ParameterPredicate, Perm, Place, Predicate, Ty,
        Variable, VarianceKind,
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
        Predicate::Class(_kind, parameter) => check_predicate_parameter(env, parameter),
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
    pub fn prove_is_shared(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_predicate(env, Predicate::shared(a)) => ())
            ---------------------------- ("is")
            (prove_is_shared(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_is_shareable(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_predicate(env, ClassPredicate::Share.apply(a)) => ())
            ---------------------------- ("is")
            (prove_is_shareable(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_isnt_known_to_be_shared(
        env: Env,
        p: Parameter,
    ) => () {
        debug(p, env)

        (
            (if !env.assumptions().contains(&Predicate::shared(&perm)))
            (if let false = perm.meets_predicate(&env, ParameterPredicate::Shared)?)
            ---------------------------- ("isnt known to be shared")
            (prove_isnt_known_to_be_shared(env, perm) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_isnt_known_to_be_lent(
        env: Env,
        p: Parameter,
    ) => () {
        debug(p, env)

        (
            (if !env.assumptions().contains(&Predicate::lent(&perm)))
            (if let false = perm.meets_predicate(&env, ParameterPredicate::Lent)?)
            ---------------------------- ("isnt known to be lent")
            (prove_isnt_known_to_be_lent(env, perm) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_is_unique(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_predicate(env, Predicate::move_(a)) => ())
            ---------------------------- ("is-moved")
            (prove_is_unique(env, a) => ())
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

judgment_fn! {
    pub fn prove_is_my(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_is_unique(&env, &a) => ())
            (prove_is_owned(&env, &a) => ())
            ---------------------------- ("prove")
            (prove_is_my(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn prove_is_our(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (prove_is_shared(&env, &a) => ())
            (prove_is_owned(&env, &a) => ())
            ---------------------------- ("prove")
            (prove_is_our(env, a) => ())
        )
    }
}

pub fn prove_is_unique_if_some(
    env: impl Upcast<Env>,
    a: impl Upcast<Option<(Place, Parameter)>>,
) -> ProvenSet<()> {
    let a: Option<(Place, Parameter)> = a.upcast();
    match a {
        Some((_, a)) => prove_is_unique(env, a),
        None => ProvenSet::singleton(()),
    }
}

// FIXME: Why does the judgment function below not work but the function above does?
// judgment_fn! {
//     pub fn prove_is_unique_if_some(
//         env: Env,
//         a: Option<Parameter>,
//     ) => () {
//         debug(a, env)

//         (
//             (prove_predicate(env, Predicate::move_(a)) => ())
//             ---------------------------- ("is-move-some")
//             (prove_is_unique_if_some(env, Some::<Parameter>(a)) => ()) // annoying type hint that doesn't seem like it should be needed
//         )

//         (
//             ---------------------------- ("is-move-none")
//             (prove_is_unique_if_some(_env, Option::<Parameter>::None) => ())
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
            (prove_class_predicate(env, kind, parameter) => ())
            ---------------------------- ("parameter")
            (prove_predicate(env, Predicate::Class(kind, parameter)) => ())
        )

        (
            (variance_predicate(env, kind, parameter) => ())
            ---------------------------- ("variance")
            (prove_predicate(env, Predicate::Variance(kind, parameter)) => ())
        )
    }
}

judgment_fn! {
    fn prove_class_predicate(
        env: Env,
        kind: ClassPredicate,
        parameter: Parameter,
    ) => () {
        debug(kind, parameter, env)

        // Classes meet a class predicate if they are declared to and their type parameters do as well.
        (
            (if let true = env.meets_class_predicate(&name, predicate)?)
            (for_all(parameters, &|parameter| prove_predicate(&env, predicate.apply(parameter))) => ())
            ----------------------------- ("class")
            (prove_class_predicate(env, predicate, NamedTy { name, parameters }) => ())
        )

        // A `P T` combo can only be guard if `P = my`.
        // In particular, `mut[d] GuardClass` is not itself `guard`.
        (
            (prove_is_my(&env, &perm) => ())
            (prove_predicate(&env, ClassPredicate::Guard.apply(&*ty)) => ())
            ----------------------------- ("`P T` is share if `T` is share")
            (prove_class_predicate(env, ClassPredicate::Guard, Ty::ApplyPerm(perm, ty)) => ())
        )

        (
            (prove_predicate(&env, ClassPredicate::Share.apply(&*ty)) => ())
            ----------------------------- ("`P T` is share if `T` is share")
            (prove_class_predicate(env, ClassPredicate::Share, Ty::ApplyPerm(_, ty)) => ())
        )

        (
            (prove_is_lent(&env, perm) => ())
            ----------------------------- ("`lent T` is share")
            (prove_class_predicate(env, ClassPredicate::Share, Ty::ApplyPerm(perm, _)) => ())
        )

        (
            (prove_is_shared(&env, perm) => ())
            ----------------------------- ("`shared T` is share")
            (prove_class_predicate(env, ClassPredicate::Share, Ty::ApplyPerm(perm, _)) => ())
        )

        (
            (prove_is_our(env, ty) => ())
            ----------------------------- ("our types")
            (prove_class_predicate(env, ClassPredicate::Our, ty) => ())
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

        // FIXME: Is this right? What about e.g. `struct Foo[perm P, ty T] { x: T, y: P ref[x] String }`
        // or other such things? and what about `moved[x]`?

        (
            ----------------------------- ("shared")
            (variance_predicate(_env, _kind, Perm::Rf(_)) => ())
        )

        (
            (for_all(places, &|place| variance_predicate_place(&env, kind, place)) => ())
            ----------------------------- ("leased")
            (variance_predicate(env, kind, Perm::Mt(places)) => ())
        )

        (
            (for_all(places, &|place| variance_predicate_place(&env, kind, place)) => ())
            ----------------------------- ("given")
            (variance_predicate(env, kind, Perm::Mv(places)) => ())
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
            ParameterPredicate::Shared | ParameterPredicate::Lent => {
                Any(self.0.clone()).meets_predicate(env, predicate)
            }
            ParameterPredicate::Unique | ParameterPredicate::Owned => {
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
        if env.is_our_ty(name)? {
            // Value types are copy iff all of their parameters are copy.
            match k {
                ParameterPredicate::Shared => {
                    All(parameters).meets_predicate(env, ParameterPredicate::Shared)
                }
                ParameterPredicate::Unique => {
                    Any(parameters).meets_predicate(env, ParameterPredicate::Unique)
                }
                ParameterPredicate::Owned => {
                    All(parameters).meets_predicate(env, ParameterPredicate::Owned)
                }
                ParameterPredicate::Lent => Ok(false),
            }
        } else {
            // Classes are always move.
            match k {
                ParameterPredicate::Shared => Ok(false),
                ParameterPredicate::Unique => Ok(true),
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
                ParameterPredicate::Unique | ParameterPredicate::Owned => Ok(true),
                ParameterPredicate::Shared | ParameterPredicate::Lent => Ok(false),
            },
            crate::grammar::Perm::Our => match k {
                ParameterPredicate::Shared | ParameterPredicate::Owned => Ok(true),
                ParameterPredicate::Unique | ParameterPredicate::Lent => Ok(false),
            },
            crate::grammar::Perm::Mv(places) => Many(places).meets_predicate(env, k),
            crate::grammar::Perm::Rf(places) => {
                Many(places.iter().map(|place| RefFrom(place))).meets_predicate(env, k)
            }
            crate::grammar::Perm::Mt(places) => {
                Many(places.iter().map(|place| MutFrom(place))).meets_predicate(env, k)
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

        if rhs.meets_predicate(env, ParameterPredicate::Shared)? {
            // In this case, `(perm ty) = ty`, so just check for `ty`
            rhs.meets_predicate(env, k)
        } else {
            match k {
                ParameterPredicate::Shared | ParameterPredicate::Lent => {
                    Ok(lhs.meets_predicate(env, k)? || rhs.meets_predicate(env, k)?)
                }
                ParameterPredicate::Unique | ParameterPredicate::Owned => {
                    Ok(lhs.meets_predicate(env, k)? && rhs.meets_predicate(env, k)?)
                }
            }
        }
    }
}

/// The "essence" of leased-ness, this "subject" is composed with the
/// leased place `p` to figure out the permission of `mut[p]`.
struct SomeShared;

impl MeetsPredicate for SomeShared {
    fn meets_predicate(&self, _env: &Env, k: ParameterPredicate) -> Fallible<bool> {
        match k {
            ParameterPredicate::Shared | ParameterPredicate::Lent => Ok(true),
            ParameterPredicate::Unique | ParameterPredicate::Owned => Ok(false),
        }
    }
}

struct RefFrom<S>(S);

impl<S: MeetsPredicate> MeetsPredicate for RefFrom<S> {
    fn meets_predicate(&self, env: &Env, k: ParameterPredicate) -> Fallible<bool> {
        Compose(SomeShared, &self.0).meets_predicate(env, k)
    }
}

/// The "essence" of leased-ness, this "subject" is composed with the
/// leased place `p` to figure out the permission of `mut[p]`.
struct SomeLeased;

impl MeetsPredicate for SomeLeased {
    fn meets_predicate(&self, _env: &Env, k: ParameterPredicate) -> Fallible<bool> {
        match k {
            ParameterPredicate::Lent | ParameterPredicate::Unique => Ok(true),
            ParameterPredicate::Owned | ParameterPredicate::Shared => Ok(false),
        }
    }
}

struct MutFrom<S>(S);

impl<S: MeetsPredicate> MeetsPredicate for MutFrom<S> {
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

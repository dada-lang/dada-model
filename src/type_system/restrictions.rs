use formality_core::{cast_impl, judgment_fn, set, term, Cons, Set, SetExt as _, Upcast};

use crate::{
    dada_lang::grammar::{UniversalVar, Variable},
    grammar::{NamedTy, Parameter, Parameters, Perm, Place, Ty},
    type_system::{env::Env, places::place_ty, subtypes::is_shared},
};

#[term]
#[derive(Copy)]
pub enum Relative {
    Shared,
    Leased,
}

#[term]
pub struct Restriction {
    pub relative: Relative,
    pub place: Place,
}

#[derive(Clone, PartialOrd, Ord, PartialEq, Eq, Debug, Hash)]
pub enum Own {
    My,
    Our,
    Var(UniversalVar),
}

cast_impl!(Own);

#[derive(Clone, PartialOrd, Ord, PartialEq, Eq, Debug, Hash, Default)]
pub struct RestrictionSet {
    pub owns: Set<Own>,
    pub restrictions: Set<Restriction>,
}

cast_impl!(RestrictionSet);

impl RestrictionSet {
    pub fn our() -> Self {
        Self {
            owns: set![Own::Our],
            restrictions: set![],
        }
    }

    pub fn var(v: UniversalVar) -> Self {
        Self {
            owns: set![Own::Var(v)],
            restrictions: set![],
        }
    }

    pub fn with(&self, other: impl Upcast<RestrictionSet>) -> Self {
        let other: RestrictionSet = other.upcast();
        RestrictionSet {
            owns: other.owns.union_with(&self.owns),
            restrictions: other.restrictions.union_with(&self.restrictions),
        }
    }

    pub fn with_restrictions_from(&self, other: impl Upcast<RestrictionSet>) -> Self {
        let other: RestrictionSet = other.upcast();
        RestrictionSet {
            owns: self.owns.clone(),
            restrictions: other.restrictions.union_with(&self.restrictions),
        }
    }

    pub fn relative(relative: Relative, places: &Set<Place>) -> Self {
        Self {
            owns: set![],
            restrictions: places
                .iter()
                .map(|place| Restriction {
                    relative,
                    place: place.clone(),
                })
                .collect(),
        }
    }
}

judgment_fn! {
    pub fn restrictions(
        env: Env,
        a: Parameter,
    ) => (Env, RestrictionSet) {
        debug(a, env)

        (
            (restrictions_in(env, RestrictionSet::default(), a) => (env, rset))
            ----------------------------------- ("restrictions")
            (restrictions(env, a) => (env, rset))
        )
    }
}

judgment_fn! {
    pub fn restrictions_in(
        env: Env,
        rset: RestrictionSet,
        a: Parameter,
    ) => (Env, RestrictionSet) {
        debug(rset, a, env)

        (
            (restrictions_in_any(env, &rset, parameters) => (env, rset_p))
            (let rset = rset.with_restrictions_from(rset_p))
            -------------------------- ("ty-named-ty")
            (restrictions_in(env, rset, NamedTy { name: _, parameters }) => (env, rset))
        )

        (
            -------------------------- ("perm-my")
            (restrictions_in(env, rset, Perm::My) => (env, rset))
        )

        (
            -------------------------- ("perm-our")
            (restrictions_in(env, _rset, Perm::Our) => (env, RestrictionSet::our()))
        )

        (
            (is_shared(env, var) => env)
            (let r = RestrictionSet::var(var))
            -------------------------- ("var-sh")
            (restrictions_in(_env, _rset, Variable::UniversalVar(var)) => (env, r))
        )

        (
            (let r = RestrictionSet::var(var))
            -------------------------- ("var")
            (restrictions_in(_env, rset, Variable::UniversalVar(var)) => (env, rset.with(r)))
        )

        (
            (let rset_sh = RestrictionSet::relative(Relative::Shared, &places))
            (restrictions_given_from(env, &rset_sh, places) => (env, rset_p))
            -------------------------- ("perm-shared")
            (restrictions_in(env, _rset, Perm::Shared(places)) => (env, rset_sh.with_restrictions_from(rset_p)))
        )

        (
            (let rset_l = rset.with(RestrictionSet::relative(Relative::Leased, &places)))
            (restrictions_given_from(env, &rset_l, places) => (env, rset_p))
            -------------------------- ("perm-leased")
            (restrictions_in(env, rset, Perm::Leased(places)) => (env, rset_l.with_restrictions_from(rset_p)))
        )

        (
            (restrictions_given_from(env, rset, places) => (env, rset))
            -------------------------- ("perm-given")
            (restrictions_in(_env, rset, Perm::Given(places)) => (env, rset))
        )

        (
            (restrictions_in(env, rset, perm) => (env, rset))
            (restrictions_in(env, rset, &*ty) => (env, rset))
            -------------------------- ("ty-apply-perm")
            (restrictions_in(env, rset, Ty::ApplyPerm(perm, ty)) => (env, rset))
        )

        (
            (restrictions_in(env, rset, &*perm1) => (env, rset))
            (restrictions_in(env, rset, &*perm2) => (env, rset))
            -------------------------- ("perm-apply")
            (restrictions_in(env, rset, Perm::Apply(perm1, perm2)) => (env, rset))
        )

        (
            (restrictions_in_any(env, rset, vec![&*a, &*b]) => (env, rset))
            -------------------------- ("ty-or")
            (restrictions_in(env, rset, Ty::Or(a, b)) => (env, rset))
        )

        (
            (restrictions_in_any(env, rset, vec![&*a, &*b]) => (env, rset))
            -------------------------- ("perm-or")
            (restrictions_in(env, rset, Perm::Or(a, b)) => (env, rset))
        )
    }
}

judgment_fn! {
    pub fn restrictions_in_any(
        env: Env,
        rset: RestrictionSet,
        ps: Parameters,
    ) => (Env, RestrictionSet) {
        debug(rset, ps, env)

        (
            -------------------------- ("nil")
            (restrictions_in_any(env, rset, ()) => (env, rset))
        )

        (
            (restrictions_in(env, &rset, p) => (env, rset1))
            (restrictions_in_any(env, &rset, &qs) => (env, rset2))
            -------------------------- ("cons")
            (restrictions_in_any(env, rset, Cons(p, qs)) => (env, rset1.with(rset2)))
        )
    }
}

judgment_fn! {
    pub fn restrictions_given_from(
        env: Env,
        rset: RestrictionSet,
        ps: Set<Place>,
    ) => (Env, RestrictionSet) {
        debug(rset, ps, env)

        (
            -------------------------- ("nil")
            (restrictions_given_from(env, rset, ()) => (env, rset))
        )

        (
            (place_ty(&env, p) => ty)
            (restrictions_in(&env, &rset, ty) => (env, rset1))
            (restrictions_given_from(env, &rset, &qs) => (env, rset2))
            -------------------------- ("cons")
            (restrictions_given_from(env, rset, Cons(p, qs)) => (env, rset1.with(rset2)))
        )
    }
}

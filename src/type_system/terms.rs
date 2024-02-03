use formality_core::{cast_impl, judgment_fn, set, term, Cons, Set, SetExt as _, Upcast};

use crate::{
    dada_lang::grammar::{UniversalVar, Variable},
    grammar::{NamedTy, Parameter, Parameters, Perm, Place, Ty},
    type_system::{env::Env, places::place_ty, subtypes::is_shared},
};

#[term]
#[derive(Copy)]
pub enum LienKind {
    Shared,
    Leased,
}

#[term]
pub struct Lien {
    pub kind: LienKind,
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
pub struct Terms {
    pub owns: Set<Own>,
    pub liens: Set<Lien>,
}

cast_impl!(Terms);

impl Terms {
    pub fn our() -> Self {
        Self {
            owns: set![Own::Our],
            liens: set![],
        }
    }

    pub fn var(v: UniversalVar) -> Self {
        Self {
            owns: set![Own::Var(v)],
            liens: set![],
        }
    }

    pub fn with(&self, other: impl Upcast<Terms>) -> Self {
        let other: Terms = other.upcast();
        Terms {
            owns: other.owns.union_with(&self.owns),
            liens: other.liens.union_with(&self.liens),
        }
    }

    pub fn with_liens_from(&self, other: impl Upcast<Terms>) -> Self {
        let other: Terms = other.upcast();
        Terms {
            owns: self.owns.clone(),
            liens: other.liens.union_with(&self.liens),
        }
    }

    pub fn lien(kind: LienKind, places: &Set<Place>) -> Self {
        Self {
            owns: set![],
            liens: places
                .iter()
                .map(|place| Lien {
                    kind,
                    place: place.clone(),
                })
                .collect(),
        }
    }
}

judgment_fn! {
    pub fn terms(
        env: Env,
        a: Parameter,
    ) => (Env, Terms) {
        debug(a, env)

        (
            (terms_in(env, Terms::default(), a) => (env, terms))
            ----------------------------------- ("restrictions")
            (terms(env, a) => (env, terms))
        )
    }
}

judgment_fn! {
    pub fn terms_in(
        env: Env,
        terms: Terms,
        a: Parameter,
    ) => (Env, Terms) {
        debug(terms, a, env)

        (
            (terms_in_any(env, &terms, parameters) => (env, terms_p))
            (let terms = terms.with_liens_from(terms_p))
            -------------------------- ("ty-named-ty")
            (terms_in(env, terms, NamedTy { name: _, parameters }) => (env, terms))
        )

        (
            -------------------------- ("perm-my")
            (terms_in(env, terms, Perm::My) => (env, terms))
        )

        (
            -------------------------- ("perm-our")
            (terms_in(env, _terms, Perm::Our) => (env, Terms::our()))
        )

        (
            (is_shared(env, var) => env)
            (let r = Terms::var(var))
            -------------------------- ("var-sh")
            (terms_in(_env, _terms, Variable::UniversalVar(var)) => (env, r))
        )

        (
            (let r = Terms::var(var))
            -------------------------- ("var")
            (terms_in(_env, terms, Variable::UniversalVar(var)) => (env, terms.with(r)))
        )

        (
            (let terms_sh = Terms::lien(LienKind::Shared, &places))
            (terms_given_from(env, &terms_sh, places) => (env, terms_p))
            -------------------------- ("perm-shared")
            (terms_in(env, _terms, Perm::Shared(places)) => (env, terms_sh.with_liens_from(terms_p)))
        )

        (
            (let terms_l = terms.with(Terms::lien(LienKind::Leased, &places)))
            (terms_given_from(env, &terms_l, places) => (env, terms_p))
            -------------------------- ("perm-leased")
            (terms_in(env, terms, Perm::Leased(places)) => (env, terms_l.with_liens_from(terms_p)))
        )

        (
            (terms_given_from(env, terms, places) => (env, terms))
            -------------------------- ("perm-given")
            (terms_in(_env, terms, Perm::Given(places)) => (env, terms))
        )

        (
            (terms_in(env, terms, perm) => (env, terms))
            (terms_in(env, terms, &*ty) => (env, terms))
            -------------------------- ("ty-apply-perm")
            (terms_in(env, terms, Ty::ApplyPerm(perm, ty)) => (env, terms))
        )

        (
            (terms_in(env, terms, &*perm1) => (env, terms))
            (terms_in(env, terms, &*perm2) => (env, terms))
            -------------------------- ("perm-apply")
            (terms_in(env, terms, Perm::Apply(perm1, perm2)) => (env, terms))
        )

        (
            (terms_in_any(env, terms, vec![&*a, &*b]) => (env, terms))
            -------------------------- ("ty-or")
            (terms_in(env, terms, Ty::Or(a, b)) => (env, terms))
        )

        (
            (terms_in_any(env, terms, vec![&*a, &*b]) => (env, terms))
            -------------------------- ("perm-or")
            (terms_in(env, terms, Perm::Or(a, b)) => (env, terms))
        )
    }
}

judgment_fn! {
    pub fn terms_in_any(
        env: Env,
        terms: Terms,
        ps: Parameters,
    ) => (Env, Terms) {
        debug(terms, ps, env)

        (
            -------------------------- ("nil")
            (terms_in_any(env, terms, ()) => (env, terms))
        )

        (
            (terms_in(env, &terms, p) => (env, terms1))
            (terms_in_any(env, &terms, &qs) => (env, terms2))
            -------------------------- ("cons")
            (terms_in_any(env, terms, Cons(p, qs)) => (env, terms1.with(terms2)))
        )
    }
}

judgment_fn! {
    pub fn terms_given_from(
        env: Env,
        terms: Terms,
        ps: Set<Place>,
    ) => (Env, Terms) {
        debug(terms, ps, env)

        (
            -------------------------- ("nil")
            (terms_given_from(env, terms, ()) => (env, terms))
        )

        (
            (place_ty(&env, p) => ty)
            (terms_in(&env, &terms, ty) => (env, terms1))
            (terms_given_from(env, &terms, &qs) => (env, terms2))
            -------------------------- ("cons")
            (terms_given_from(env, terms, Cons(p, qs)) => (env, terms1.with(terms2)))
        )
    }
}

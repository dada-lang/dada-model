use formality_core::{cast_impl, judgment_fn, set, term, Cons, Set, SetExt as _, Upcast};

use crate::{
    dada_lang::grammar::{UniversalVar, Variable},
    grammar::{NamedTy, Parameter, Parameters, Perm, Place, Ty, TypeName},
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

#[derive(Clone, PartialOrd, Ord, PartialEq, Eq, Debug, Hash, Default)]
pub struct Terms {
    /// If true, the value is shared (i.e., copyable, accessible from an unknown number of other places).
    pub shared: bool,

    /// If true, the value is leased (i.e., accessed by pointer from some particular other place).
    pub leased: bool,

    /// The set of universal variables referenced within, and the terms in which they appeared.
    pub vars: Set<(Terms, UniversalVar)>,

    /// The set of named types referenced within, and the terms in which they appeared.
    pub named_tys: Set<(Terms, NamedTy)>,

    /// The set of liens we have on places.
    pub liens: Set<Lien>,
}

cast_impl!(Terms);

impl Terms {
    /// Terms for a shared, owned value: no context is needed.
    pub fn our() -> Self {
        Self {
            shared: true,
            leased: false,
            vars: set![],
            named_tys: set![],
            liens: set![],
        }
    }

    /// Terms for a shared variable: since the variable is shared,
    /// no context is needed.
    pub fn shared_var(v: UniversalVar) -> Self {
        Self {
            shared: true,
            leased: false,
            vars: set![(Terms::default(), v)],
            named_tys: set![],
            liens: set![],
        }
    }

    /// Terms for a lien on `places`.
    pub fn shared_liens(places: &Set<Place>) -> Self {
        Self {
            shared: true,
            leased: false,
            vars: set![],
            named_tys: set![],
            liens: places
                .iter()
                .map(|place| Lien {
                    kind: LienKind::Shared,
                    place: place.clone(),
                })
                .collect(),
        }
    }

    /// Union one set of terms with another.
    pub fn union(&self, other: impl Upcast<Terms>) -> Self {
        let other: Terms = other.upcast();
        Terms {
            shared: self.shared || other.shared,
            leased: self.leased || other.leased,
            vars: other.vars.union_with(&self.vars),
            named_tys: other.named_tys.union_with(&self.named_tys),
            liens: other.liens.union_with(&self.liens),
        }
    }

    /// Extend `self` with leases on `places`.
    pub fn with_leases(mut self, places: &Set<Place>) -> Self {
        self.leased = true;
        self.liens.extend(places.iter().map(|place| Lien {
            kind: LienKind::Leased,
            place: place.clone(),
        }));
        self
    }

    pub fn with_named_ty(mut self, name: &TypeName, parameters: &Parameters) -> Self {
        self.named_tys.insert((
            self.clone(),
            NamedTy {
                name: name.clone(),
                parameters: parameters.clone(),
            },
        ));
        self
    }

    /// Add a universal variable into these terms.
    pub fn with_var(mut self, v: UniversalVar) -> Self {
        self.vars.insert((self.clone(), v));
        self
    }

    /// Union the liens from `other` into `self`.
    pub fn with_liens_from(&self, other: impl Upcast<Terms>) -> Self {
        let other: Terms = other.upcast();
        Terms {
            shared: self.shared,
            leased: self.leased,
            vars: self.vars.clone(),
            named_tys: self.named_tys.clone(),
            liens: other.liens.union_with(&self.liens),
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
            (let terms = terms.with_named_ty(&name, &parameters))
            (union_terms(env, Terms::default(), &parameters) => (env, terms_p))
            -------------------------- ("ty-named-ty")
            (terms_in(env, terms, NamedTy { name, parameters }) => (env, terms.with_liens_from(terms_p)))
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
            (let r = Terms::shared_var(var))
            -------------------------- ("var-sh")
            (terms_in(_env, _terms, Variable::UniversalVar(var)) => (env, r))
        )

        (
            -------------------------- ("var")
            (terms_in(_env, terms, Variable::UniversalVar(var)) => (env, terms.with_var(var)))
        )

        (
            (let terms_sh = Terms::shared_liens(&places))
            (terms_from_places(env, &terms_sh, places) => (env, terms_p))
            -------------------------- ("perm-shared")
            (terms_in(env, _terms, Perm::Shared(places)) => (env, terms_sh.with_liens_from(terms_p)))
        )

        (
            (let terms_l = terms.with_leases(&places))
            (terms_from_places(env, &terms_l, places) => (env, terms_p))
            -------------------------- ("perm-leased")
            (terms_in(env, terms, Perm::Leased(places)) => (env, terms_l.with_liens_from(terms_p)))
        )

        (
            (terms_from_places(env, terms, places) => (env, terms))
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
            (union_terms(env, terms, vec![&*a, &*b]) => (env, terms))
            -------------------------- ("ty-or")
            (terms_in(env, terms, Ty::Or(a, b)) => (env, terms))
        )

        (
            (union_terms(env, terms, vec![&*a, &*b]) => (env, terms))
            -------------------------- ("perm-or")
            (terms_in(env, terms, Perm::Or(a, b)) => (env, terms))
        )
    }
}

judgment_fn! {
    /// Union of the terms required to keep each parameter in `ps` valid.
    pub fn union_terms(
        env: Env,
        terms: Terms,
        ps: Parameters,
    ) => (Env, Terms) {
        debug(terms, ps, env)

        (
            -------------------------- ("nil")
            (union_terms(env, terms, ()) => (env, terms))
        )

        (
            (terms_in(env, &terms, p) => (env, terms1))
            (union_terms(env, &terms, &qs) => (env, terms2))
            -------------------------- ("cons")
            (union_terms(env, terms, Cons(p, qs)) => (env, terms1.union(terms2)))
        )
    }
}

judgment_fn! {
    /// Terms required to keep the places `ps` valid.
    pub fn terms_from_places(
        env: Env,
        terms: Terms,
        ps: Set<Place>,
    ) => (Env, Terms) {
        debug(terms, ps, env)

        (
            -------------------------- ("nil")
            (terms_from_places(env, terms, ()) => (env, terms))
        )

        (
            (place_ty(&env, p) => ty)
            (terms_in(&env, &terms, ty) => (env, terms1))
            (terms_from_places(env, &terms, &qs) => (env, terms2))
            -------------------------- ("cons")
            (terms_from_places(env, terms, Cons(p, qs)) => (env, terms1.union(terms2)))
        )
    }
}

use formality_core::{cast_impl, judgment_fn, set, Cons, Set, Upcast};

use crate::{
    grammar::{
        IsCopy, IsLeased, IsLent, IsMoved, IsOwned, IsShared, NamedTy, Parameter, Perm, Place, Ty,
        UniversalVar, Variable,
    },
    type_system::places::place_ty,
};

use super::env::Env;

/// "Red(uced) terms" are derived from user [`Parameter`][] terms
/// and represent the final, reduced form of a permission or type.
/// There is a single unified format for all [kinds](`crate::dada_lang::ParameterKind`)
/// of [`Parameter`][] terms. All terms are reduced to a [`RedPerms`][] and a [`RedTy`][],
/// with parameters of kind [`ParameterKind::Perm`][] being represented
/// using [`RedTy::None`][].
#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct RedTerm {
    pub perms: RedPerms,
    pub ty: RedTy,
}

cast_impl!(RedTerm);

/// "Red(uced) types" are derived from user [`Ty`][] terms
/// and represent the core type of the underlying value.
/// Unlike [`Ty`][] however they represent only the type itself
/// and not the permissions on that type-- the full info is captured
/// in the [`RedTerm`][] that is created from the [`Ty`][].
/// Another wrinkle is that [`RedTy`][] values can be created from
/// any generic term, including permissions, in which case the
/// [`RedTy`] variant is [`RedTy::None`].
#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum RedTy {
    /// Generic type variable.
    Var(UniversalVar),

    /// Named type.
    NamedTy(NamedTy),

    /// No data at all -- this occurs when we ask for the "lien data" of a permission.
    None,
}

cast_impl!(RedTy);
cast_impl!(RedTy::Var(UniversalVar));
cast_impl!(RedTy::NamedTy(NamedTy));

/// "Red(uced) perms" are derived from the [`Perm`][] terms
/// written by users. They indicate the precise implications
/// of a permission. Many distinct [`Perm`][] terms can
/// be reduced to the same `RedPerms`. For example:
///
/// * `leased[d1] our` and `our` are equivalent;
/// * `leased[d1] leased[d2]` and `leased[d1, d2]` are equivalent;
/// * and so forth.
///
/// In thinking about red-perms it is helpful to remember
/// the permission matrix:
///
/// |         | `move`       | `copy`                          |
/// |---------|--------------|---------------------------------|
/// | `owned` | `my`         | `our`                           |
/// | `lent`  | `leased[..]` | `shared[..]`,  `our leased[..]` |
///
/// All red perms represent something in this matrix (modulo generics).
#[derive(Clone, Debug, Default, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct RedPerms {
    /// Is this value copied (and hence copyable)?
    /// If true, this permission is something in the "copied" column.
    pub copied: bool,

    /// What places is this permission shared from? (if any)
    ///
    /// If non-empty, this permission is "lent".
    pub shared_from: Set<Place>,

    /// What places is this permission shared from? (if any)
    ///
    /// If non-empty, this permission is "lent".
    pub leased_from: Set<Place>,

    /// What generic variables are involved? This is the tricky widget
    /// because we don't know what permissions they'll be instantiated
    /// with except via bounds in the environment.
    pub variables: Set<UniversalVar>,
}

cast_impl!(RedPerms);

impl RedPerms {
    pub fn union(&self, other: impl Upcast<RedPerms>) -> RedPerms {
        let other: RedPerms = other.upcast();
        RedPerms {
            copied: self.copied || other.copied,
            shared_from: self
                .shared_from
                .union(&other.shared_from)
                .cloned()
                .collect(),
            leased_from: self
                .leased_from
                .union(&other.leased_from)
                .cloned()
                .collect(),
            variables: self.variables.union(&other.variables).cloned().collect(),
        }
    }

    /// Represents a `my` permission.
    pub fn my() -> RedPerms {
        RedPerms {
            copied: false,
            shared_from: set![],
            leased_from: set![],
            variables: set![],
        }
    }

    /// Represents an `our` permission.
    pub fn our() -> RedPerms {
        RedPerms {
            copied: true,
            shared_from: set![],
            leased_from: set![],
            variables: set![],
        }
    }

    /// Represents a permission shared from a set of places.
    pub fn shared(places: impl Upcast<Set<Place>>) -> RedPerms {
        RedPerms {
            copied: true,
            shared_from: places.upcast(),
            leased_from: set![],
            variables: set![],
        }
    }

    /// Represents a permission leased from a set of places.
    pub fn leased(places: impl Upcast<Set<Place>>) -> RedPerms {
        RedPerms {
            copied: false,
            shared_from: set![],
            leased_from: places.upcast(),
            variables: set![],
        }
    }

    /// Represents a permission variable.
    pub fn var(v: impl Upcast<UniversalVar>) -> RedPerms {
        RedPerms {
            copied: false,
            shared_from: set![],
            leased_from: set![],
            variables: set![v.upcast()],
        }
    }

    /// True if this lien-set represents a *copyable* term.
    ///
    /// False means the value is not known to be copyable, not that it is not copyable.
    pub fn is_copy(&self, env: &Env) -> bool {
        self.copied
            || self
                .variables
                .iter()
                .any(|v| env.is(&v, IsCopy) || env.is(&v, IsShared))
    }

    /// True if this lien-set represents a *copyable* term.
    ///
    /// False means the value is not known to be copyable, not that it is not copyable.
    pub fn is_moved(&self, env: &Env) -> bool {
        !self.copied
            && self
                .variables
                .iter()
                .all(|v| env.is(&v, IsMoved) || env.is(&v, IsLeased))
    }

    /// True if this lien-set represents a *lent* term.
    ///
    /// False means the value is not known to be lent, not that it is not lent.
    pub fn is_lent(&self, env: &Env) -> bool {
        !self.shared_from.is_empty()
            || !self.leased_from.is_empty()
            || self
                .variables
                .iter()
                .any(|v| env.is(&v, IsLent) || env.is(&v, IsLeased) || env.is(&v, IsShared))
    }

    /// True if this lien-set represents an *owned* term.
    ///
    /// False means the value is not known to be owned, not that it is not owned.
    pub fn is_owned(&self, env: &Env) -> bool {
        self.shared_from.is_empty()
            && self.leased_from.is_empty()
            && self.variables.iter().all(|v| env.is(&v, IsOwned))
    }

    /// True if this lien-set represents a *leased* term.
    ///
    /// False means the value is not known to be leased, not that it is not leased.
    pub fn is_leased(&self, env: &Env) -> bool {
        !self.is_copy(env)
            && !self.is_owned(env)
            && (!self.leased_from.is_empty() || self.variables.iter().any(|v| env.is(&v, IsLeased)))
    }

    /// True if this term cannot be leased.
    ///
    /// False means the value is not known to be not leased, not that it is leased.
    pub fn layout(&self, env: &Env) -> Layout {
        if self.is_copy(env) {
            return Layout::Value;
        }

        if self.is_owned(env) {
            return Layout::Value;
        }

        if self.is_leased(env) {
            return Layout::Leased;
        }

        let mut modulo = set![];
        for v in &self.variables {
            // If any of these predicates are known, we understand these variables'
            // contribution to the layout.
            if env.is(&v, IsOwned)
                || env.is(&v, IsCopy)
                || env.is(&v, IsShared)
                || env.is(&v, IsLeased)
            {
                continue;
            }

            modulo.insert(v.clone());
        }

        Layout::Unknown(modulo)
    }
}

/// The *layout* of a [`Perms`] indicates what we memory layout types
/// with these permissions will have.
#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum Layout {
    /// Known to be by-value
    Value,

    /// Known to be leased
    Leased,

    /// Could not determine layout due to these variables
    Unknown(Set<UniversalVar>),
}

judgment_fn! {
    pub fn red_terms(
        env: Env,
        perms_cx: RedPerms,
        a: Parameter,
    ) => Set<RedTerm> {
        debug(a, perms_cx, env)

        (
            (red_perms(&env, p) => perms_p)
            (apply_perms(&env, &perms_cx, perms_p) => perms)
            ----------------------------------- ("perm")
            (red_terms(env, perms_cx, p: Perm) => set![RedTerm { perms: perms, ty: RedTy::None }])
        )

        (
            (red_perms(&env, l) => perms_l)
            (apply_perms(&env, &perms_cx, perms_l) => perms)
            (red_terms(&env, perms, &*r) => ld_r)
            ----------------------------------- ("ty-apply")
            (red_terms(env, perms_cx, Ty::ApplyPerm(l, r)) => ld_r)
        )

        (
            ----------------------------------- ("universal ty var")
            (red_terms(_env, perms, Ty::Var(Variable::UniversalVar(v))) => set![RedTerm { perms, ty: RedTy::Var(v) }])
        )

        (
            ----------------------------------- ("named ty")
            (red_terms(_env, perms, Ty::NamedTy(n)) => set![RedTerm { perms, ty: RedTy::NamedTy(n) }])
        )

        (
            (red_terms(&env, &perms, &*l) => ld_l)
            (red_terms(&env, &perms, &*r) => ld_r)
            ----------------------------------- ("ty or")
            (red_terms(env, perms, Ty::Or(l, r)) => set![..&ld_l, ..&ld_r])
        )

    }
}

judgment_fn! {
    pub fn reduces_to_copy(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (red_perms(&env, a) => perms)
            (if perms.is_copy(&env))
            ----------------------------------- ("my")
            (reduces_to_copy(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn reduces_to_moved(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (red_perms(&env, a) => perms)
            (if perms.is_moved(&env))
            ----------------------------------- ("my")
            (reduces_to_moved(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn reduces_to_leased(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (red_perms(&env, a) => perms)
            (if perms.is_leased(&env))
            ----------------------------------- ("my")
            (reduces_to_leased(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn red_perms(
        env: Env,
        a: Parameter,
    ) => RedPerms {
        debug(a, env)

        (
            ----------------------------------- ("my")
            (red_perms(_env, Perm::My) => RedPerms::my())
        )

        (
            ----------------------------------- ("our")
            (red_perms(_env, Perm::Our) => RedPerms::our())
        )

        (
            (perms_from_places(&env, &places) => perms_places)
            (apply_perms(&env, RedPerms::shared(&places), perms_places) => perms)
            ----------------------------------- ("shared")
            (red_perms(env, Perm::Shared(places)) => perms)
        )

        (
            (perms_from_places(&env, &places) => perms_places)
            (apply_perms(&env, RedPerms::leased(&places), perms_places) => perms)
            ----------------------------------- ("leased")
            (red_perms(env, Perm::Leased(places)) => perms)
        )

        (
            (perms_from_places(&env, places) => perms_places)
            ----------------------------------- ("given")
            (red_perms(env, Perm::Given(places)) => perms_places)
        )

        (
            ----------------------------------- ("universal var")
            (red_perms(_env, v: UniversalVar) => RedPerms::var(v))
        )

        (
            (red_perms(&env, &*l) => perms_l)
            (red_perms(&env, &*r) => perms_r)
            (apply_perms(&env, &perms_l, perms_r) => perms)
            ----------------------------------- ("perm-apply")
            (red_perms(env, Perm::Apply(l, r)) => perms)
        )

        (
            (red_perms(&env, l) => perms_l)
            (red_perms(&env, &*r) => perms_r)
            (apply_perms(&env, &perms_l, perms_r) => perms)
            ----------------------------------- ("ty-apply")
            (red_perms(env, Ty::ApplyPerm(l, r)) => perms)
        )

        (
            ----------------------------------- ("named ty")
            (red_perms(_env, Ty::NamedTy(_n)) => RedPerms::my())
        )

        (
            (red_perms(&env, &*l) => perms_l)
            (red_perms(&env, &*r) => perms_r)
            ----------------------------------- ("ty or")
            (red_perms(env, Ty::Or(l, r)) => perms_l.union(perms_r))
        )

        (
            (red_perms(&env, &*l) => perms_l)
            (red_perms(&env, &*r) => perms_r)
            ----------------------------------- ("perm or")
            (red_perms(env, Perm::Or(l, r)) => perms_l.union(perms_r))
        )

    }
}

judgment_fn! {
    fn apply_perms(
        env: Env,
        l: RedPerms,
        r: RedPerms,
    ) => RedPerms {
        debug(l, r, env)

        (
            (if r.is_copy(&env))
            ----------------------------------- ("rhs is copy")
            (apply_perms(env, _l, r) => &r)
        )

        (
            (if !r.is_copy(&env))
            ----------------------------------- ("rhs not copy")
            (apply_perms(_env, l, r) => l.union(r))
        )
    }
}

judgment_fn! {
    fn perms_from_places(
        env: Env,
        places: Set<Place>,
    ) => RedPerms {
        debug(places, env)

        (
            ----------------------------------- ("nil")
            (perms_from_places(_env, ()) => RedPerms::my())
        )

        (
            (perms_from_place(&env, place) => perms0)
            (perms_from_places(&env, &places) => perms1)
            ----------------------------------- ("cons")
            (perms_from_places(env, Cons(place, places)) => perms0.union(perms1))
        )
    }
}

judgment_fn! {
    fn perms_from_place(
        env: Env,
        place: Place,
    ) => RedPerms {
        debug(place, env)

        (
            (place_ty(&env, &place) => ty)
            (red_perms(&env, ty) => perms)
            ----------------------------------- ("place")
            (perms_from_place(env, place) => perms)
        )
    }
}

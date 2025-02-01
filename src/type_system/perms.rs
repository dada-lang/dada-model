use formality_core::{cast_impl, judgment_fn, set, Cons, Set, Upcast};

use crate::{
    grammar::{
        IsCopy, IsLeased, IsLent, IsMoved, IsOwned, IsShared, NamedTy, Parameter, Perm, Place, Ty,
        UniversalVar, Variable,
    },
    type_system::places::place_ty,
};

use super::env::Env;

/// A "lien type" is a simplified representation of a Dada type.
/// It contains a [`Data`][] describing the kind of data we
/// are working with a set of [`Lien`]s indicating what permissions
/// we have to it (and how those permissions can be invalidated by reads/writes
/// of other places).
#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct LienData {
    pub perms: Perms,
    pub data: TyData,
}

cast_impl!(LienData);

/// Describes the type of data found in a value.
#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum TyData {
    /// Generic type variable.
    Var(UniversalVar),

    /// Named type.
    NamedTy(NamedTy),

    /// No data at all -- this occurs when we ask for the "lien data" of a permission.
    None,
}

cast_impl!(TyData);
cast_impl!(TyData::Var(UniversalVar));
cast_impl!(TyData::NamedTy(NamedTy));

#[derive(Clone, Debug, Default, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct Perms {
    pub copied: bool,
    pub shared_from: Set<Place>,
    pub leased_from: Set<Place>,
    pub variables: Set<UniversalVar>,
}

cast_impl!(Perms);

impl Perms {
    pub fn union(&self, other: impl Upcast<Perms>) -> Perms {
        let other: Perms = other.upcast();
        Perms {
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
    pub fn my() -> Perms {
        Perms {
            copied: false,
            shared_from: set![],
            leased_from: set![],
            variables: set![],
        }
    }

    /// Represents an `our` permission.
    pub fn our() -> Perms {
        Perms {
            copied: true,
            shared_from: set![],
            leased_from: set![],
            variables: set![],
        }
    }

    /// Represents a permission shared from a set of places.
    pub fn shared(places: impl Upcast<Set<Place>>) -> Perms {
        Perms {
            copied: true,
            shared_from: places.upcast(),
            leased_from: set![],
            variables: set![],
        }
    }

    /// Represents a permission leased from a set of places.
    pub fn leased(places: impl Upcast<Set<Place>>) -> Perms {
        Perms {
            copied: false,
            shared_from: set![],
            leased_from: places.upcast(),
            variables: set![],
        }
    }

    /// Represents a permission variable.
    pub fn var(v: impl Upcast<UniversalVar>) -> Perms {
        Perms {
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
    pub fn is_not_leased(&self, env: &Env) -> bool {
        self.is_copy(env) || self.is_owned(env)
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
    pub fn lien_datas(
        env: Env,
        perms_cx: Perms,
        a: Parameter,
    ) => Set<LienData> {
        debug(a, perms_cx, env)

        (
            (perms(&env, p) => perms_p)
            (apply_perms(&env, &perms_cx, perms_p) => perms)
            ----------------------------------- ("perm")
            (lien_datas(env, perms_cx, p: Perm) => set![LienData { perms: perms, data: TyData::None }])
        )

        (
            (perms(&env, l) => perms_l)
            (apply_perms(&env, &perms_cx, perms_l) => perms)
            (lien_datas(&env, perms, &*r) => ld_r)
            ----------------------------------- ("ty-apply")
            (lien_datas(env, perms_cx, Ty::ApplyPerm(l, r)) => ld_r)
        )

        (
            ----------------------------------- ("universal ty var")
            (lien_datas(_env, perms, Ty::Var(Variable::UniversalVar(v))) => set![LienData { perms, data: TyData::Var(v) }])
        )

        (
            ----------------------------------- ("named ty")
            (lien_datas(_env, perms, Ty::NamedTy(n)) => set![LienData { perms, data: TyData::NamedTy(n) }])
        )

        (
            (lien_datas(&env, &perms, &*l) => ld_l)
            (lien_datas(&env, &perms, &*r) => ld_r)
            ----------------------------------- ("ty or")
            (lien_datas(env, perms, Ty::Or(l, r)) => set![..&ld_l, ..&ld_r])
        )

    }
}

judgment_fn! {
    pub fn perms_is_copy(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (perms(&env, a) => perms)
            (if perms.is_copy(&env))
            ----------------------------------- ("my")
            (perms_is_copy(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn perms_is_moved(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (perms(&env, a) => perms)
            (if perms.is_moved(&env))
            ----------------------------------- ("my")
            (perms_is_moved(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn perms_is_leased(
        env: Env,
        a: Parameter,
    ) => () {
        debug(a, env)

        (
            (perms(&env, a) => perms)
            (if perms.is_leased(&env))
            ----------------------------------- ("my")
            (perms_is_leased(env, a) => ())
        )
    }
}

judgment_fn! {
    pub fn perms(
        env: Env,
        a: Parameter,
    ) => Perms {
        debug(a, env)

        (
            ----------------------------------- ("my")
            (perms(_env, Perm::My) => Perms::my())
        )

        (
            ----------------------------------- ("our")
            (perms(_env, Perm::Our) => Perms::our())
        )

        (
            (perms_from_places(&env, &places) => perms_places)
            (apply_perms(&env, Perms::shared(&places), perms_places) => perms)
            ----------------------------------- ("shared")
            (perms(env, Perm::Shared(places)) => perms)
        )

        (
            (perms_from_places(&env, &places) => perms_places)
            (apply_perms(&env, Perms::leased(&places), perms_places) => perms)
            ----------------------------------- ("leased")
            (perms(env, Perm::Leased(places)) => perms)
        )

        (
            (perms_from_places(&env, places) => perms_places)
            ----------------------------------- ("given")
            (perms(env, Perm::Given(places)) => perms_places)
        )

        (
            ----------------------------------- ("universal var")
            (perms(_env, v: UniversalVar) => Perms::var(v))
        )

        (
            (perms(&env, &*l) => perms_l)
            (perms(&env, &*r) => perms_r)
            (apply_perms(&env, &perms_l, perms_r) => perms)
            ----------------------------------- ("perm-apply")
            (perms(env, Perm::Apply(l, r)) => perms)
        )

        (
            (perms(&env, l) => perms_l)
            (perms(&env, &*r) => perms_r)
            (apply_perms(&env, &perms_l, perms_r) => perms)
            ----------------------------------- ("ty-apply")
            (perms(env, Ty::ApplyPerm(l, r)) => perms)
        )

        (
            ----------------------------------- ("named ty")
            (perms(_env, Ty::NamedTy(_n)) => Perms::my())
        )

        (
            (perms(&env, &*l) => perms_l)
            (perms(&env, &*r) => perms_r)
            ----------------------------------- ("ty or")
            (perms(env, Ty::Or(l, r)) => perms_l.union(perms_r))
        )

        (
            (perms(&env, &*l) => perms_l)
            (perms(&env, &*r) => perms_r)
            ----------------------------------- ("perm or")
            (perms(env, Perm::Or(l, r)) => perms_l.union(perms_r))
        )

    }
}

judgment_fn! {
    fn apply_perms(
        env: Env,
        l: Perms,
        r: Perms,
    ) => Perms {
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
    ) => Perms {
        debug(places, env)

        (
            ----------------------------------- ("nil")
            (perms_from_places(_env, ()) => Perms::my())
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
    ) => Perms {
        debug(place, env)

        (
            (place_ty(&env, &place) => ty)
            (perms(&env, ty) => perms)
            ----------------------------------- ("place")
            (perms_from_place(env, place) => perms)
        )
    }
}

use formality_core::{cast_impl, judgment_fn, set, Cons, Set, Upcast};

use crate::{
    grammar::{
        IsCopy, IsLeased, IsLent, IsMoved, IsOwned, NamedTy, Parameter, Perm, Place, Ty,
        UniversalVar, Variable,
    },
    type_system::{places::place_ty, quantifiers::for_all},
};

use super::env::Env;

/// A "lien type" is a simplified representation of a Dada type.
/// It contains a [`Data`][] describing the kind of data we
/// are working with a set of [`Lien`]s indicating what permissions
/// we have to it (and how those permissions can be invalidated by reads/writes
/// of other places).
#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct LienData {
    pub liens: LienSet,
    pub data: Data,
}

cast_impl!(LienData);

/// Describes the type of data found in a value.
#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum Data {
    /// Generic type variable.
    Var(UniversalVar),

    /// Named type.
    NamedTy(NamedTy),

    /// No data at all -- this occurs when we ask for the "lien data" of a permission.
    None,
}

cast_impl!(Data);
cast_impl!(Data::Var(UniversalVar));
cast_impl!(Data::NamedTy(NamedTy));

#[derive(Clone, Default, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct LienSet {
    pub elements: Set<Lien>,
}

cast_impl!(LienSet);

impl std::fmt::Debug for LienSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.elements, f)
    }
}

impl LienSet {
    pub fn union(&self, other: impl Upcast<LienSet>) -> LienSet {
        let mut result = other.upcast();
        result.elements.extend(self.elements.iter().cloned());
        result
    }
}

impl<'a> IntoIterator for &'a LienSet {
    type Item = &'a Lien;
    type IntoIter = std::collections::btree_set::Iter<'a, Lien>;

    fn into_iter(self) -> Self::IntoIter {
        self.elements.iter()
    }
}

/// *Liens* are granular elements that, collectively, represent a *permission*.
/// They indicate what we can do with a value as well as what we kinds of actions would invalidate the value.
#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum Lien {
    /// The value can be freely copied with the `.copy` operator.
    Copy,

    /// The value contains "lent" data from other values (this arises from a `shared` or `leased` permission).
    Lent,

    /// The value is invalidated if `Place` is accessed.
    Shared(Place),

    /// The value is invalidated if `Place` is written to.
    Leased(Place),

    /// The value contains whatever permissions come from the generic parameter.
    /// This can be a permission variable *or* a type variable. If a type variable,
    /// it indicates the liens derived from that type.
    Var(UniversalVar),
}

cast_impl!(Lien);
cast_impl!(Lien::Var(UniversalVar));

judgment_fn! {
    pub fn lien_datas(
        env: Env,
        liens_cx: LienSet,
        a: Parameter,
    ) => Set<LienData> {
        debug(a, liens_cx, env)

        (
            (liens(&env, p) => liens_p)
            (apply_liens(&env, &liens_cx, liens_p) => liens)
            ----------------------------------- ("perm")
            (lien_datas(env, liens_cx, p: Perm) => set![LienData { liens: liens, data: Data::None }])
        )

        (
            (liens(&env, l) => liens_l)
            (apply_liens(&env, &liens_cx, liens_l) => liens)
            (lien_datas(&env, liens, &*r) => ld_r)
            ----------------------------------- ("ty-apply")
            (lien_datas(env, liens_cx, Ty::ApplyPerm(l, r)) => ld_r)
        )

        (
            ----------------------------------- ("universal ty var")
            (lien_datas(_env, liens, Ty::Var(Variable::UniversalVar(v))) => set![LienData { liens, data: Data::Var(v) }])
        )

        (
            ----------------------------------- ("named ty")
            (lien_datas(_env, liens, Ty::NamedTy(n)) => set![LienData { liens, data: Data::NamedTy(n) }])
        )

        (
            (lien_datas(&env, &liens, &*l) => ld_l)
            (lien_datas(&env, &liens, &*r) => ld_r)
            ----------------------------------- ("ty or")
            (lien_datas(env, liens, Ty::Or(l, r)) => Union(&ld_l, &ld_r))
        )

    }
}

judgment_fn! {
    pub fn liens(
        env: Env,
        a: Parameter,
    ) => LienSet {
        debug(a, env)

        (
            ----------------------------------- ("my")
            (liens(_env, Perm::My) => ())
        )

        (
            ----------------------------------- ("our")
            (liens(_env, Perm::Our) => set![Lien::Copy])
        )

        (
            (liens_from_places(&env, &places) => liens_places)
            (let shared_places = places.iter().map(|p| Lien::Shared(p.upcast())))
            (let liens_sh = set![Lien::Copy, Lien::Lent, ..shared_places])
            (apply_liens(&env, liens_sh, liens_places) => liens)
            ----------------------------------- ("shared")
            (liens(env, Perm::Shared(places)) => liens)
        )

        (
            (liens_from_places(&env, &places) => liens_places)
            (let leased_places = places.iter().map(|p| Lien::Leased(p.upcast())))
            (let liens_l = set![Lien::Lent, ..leased_places])
            (apply_liens(&env, liens_l, liens_places) => liens)
            ----------------------------------- ("leased")
            (liens(env, Perm::Leased(places)) => liens)
        )

        (
            (liens_from_places(&env, places) => liens_places)
            ----------------------------------- ("given")
            (liens(env, Perm::Given(places)) => liens_places)
        )

        (
            (if env.is(&v, IsOwned))
            (if env.is(&v, IsMoved))
            ----------------------------------- ("universal var: my")
            (liens(env, v: UniversalVar) => ())
        )


        (
            ----------------------------------- ("universal var")
            (liens(_env, v: UniversalVar) => set![v])
        )

        (
            (liens(&env, &*l) => liens_l)
            (liens(&env, &*r) => liens_r)
            (apply_liens(&env, &liens_l, liens_r) => liens)
            ----------------------------------- ("perm-apply")
            (liens(env, Perm::Apply(l, r)) => liens)
        )

        (
            (liens(&env, l) => liens_l)
            (liens(&env, &*r) => liens_r)
            (apply_liens(&env, &liens_l, liens_r) => liens)
            ----------------------------------- ("ty-apply")
            (liens(env, Ty::ApplyPerm(l, r)) => liens)
        )

        (
            ----------------------------------- ("named ty")
            (liens(_env, Ty::NamedTy(_n)) => ())
        )

        (
            (liens(&env, &*l) => liens_l)
            (liens(&env, &*r) => liens_r)
            ----------------------------------- ("ty or")
            (liens(env, Ty::Or(l, r)) => Union(&liens_l, liens_r))
        )

        (
            (liens(&env, &*l) => liens_l)
            (liens(&env, &*r) => liens_r)
            ----------------------------------- ("perm or")
            (liens(env, Perm::Or(l, r)) => Union(&liens_l, liens_r))
        )

    }
}

judgment_fn! {
    fn apply_liens(
        env: Env,
        l: LienSet,
        r: LienSet,
    ) => LienSet {
        debug(l, r, env)

        (
            (lien_set_is_copy(env, &r) => ())
            ----------------------------------- ("rhs is copy")
            (apply_liens(env, _l, r) => &r)
        )

        (
            ----------------------------------- ("rhs not copy")
            (apply_liens(_env, l, r) => Union(l, r))
        )
    }
}

judgment_fn! {
    fn liens_from_places(
        env: Env,
        places: Set<Place>,
    ) => LienSet {
        debug(places, env)

        (
            ----------------------------------- ("nil")
            (liens_from_places(_env, ()) => ())
        )

        (
            (liens_from_place(&env, place) => liens0)
            (liens_from_places(&env, &places) => liens1)
            ----------------------------------- ("cons")
            (liens_from_places(env, Cons(place, places)) => Union(&liens0, liens1))
        )
    }
}

judgment_fn! {
    fn liens_from_place(
        env: Env,
        place: Place,
    ) => LienSet {
        debug(place, env)

        (
            (place_ty(&env, &place) => ty)
            (liens(&env, ty) => liens)
            ----------------------------------- ("place")
            (liens_from_place(env, place) => liens)
        )
    }
}

judgment_fn! {
    pub fn lien_set_is_copy(
        env: Env,
        liens: LienSet,
    ) => () {
        debug(liens, env)

        (
            (&liens => l)
            (lien_is_copy(&env, l) => ())
            ----------------------------------- ("some")
            (lien_set_is_copy(env, liens) => ())
        )
    }
}

judgment_fn! {
    pub fn lien_set_is_owned(
        env: Env,
        liens: LienSet,
    ) => () {
        debug(liens, env)

        (
            (for_all(&liens, &|lien| lien_is_owned(&env, lien)) => ())
            ----------------------------------- ("some")
            (lien_set_is_owned(env, liens) => ())
        )
    }
}

judgment_fn! {
    fn lien_is_copy(
        env: Env,
        lien: Lien,
    ) => () {
        debug(lien, env)

        (
            ----------------------------------- ("copy")
            (lien_is_copy(_env, Lien::Copy) => ())
        )

        (
            (if env.is(&var, IsCopy))
            ----------------------------------- ("var is copy")
            (lien_is_copy(env, Lien::Var(var)) => ())
        )
    }
}

judgment_fn! {
    fn lien_is_owned(
        env: Env,
        lien: Lien,
    ) => () {
        debug(lien, env)

        (
            (if env.is(&var, IsOwned))
            ----------------------------------- ("var is move")
            (lien_is_owned(env, Lien::Var(var)) => ())
        )
    }
}

#[derive(Clone)]
struct Union<A, B>(A, B);

impl<A, B, C> Upcast<Set<C>> for Union<A, B>
where
    A: Upcast<Set<C>>,
    B: Upcast<Set<C>>,
    C: Ord,
{
    fn upcast(self) -> Set<C> {
        let mut a: Set<C> = self.0.upcast();
        let b: Set<C> = self.1.upcast();
        a.extend(b);
        a
    }
}

impl<A, B> Upcast<LienSet> for Union<A, B>
where
    A: Upcast<LienSet>,
    B: Upcast<LienSet>,
{
    fn upcast(self) -> LienSet {
        let a: LienSet = self.0.upcast();
        a.union(self.1)
    }
}

impl Upcast<LienSet> for () {
    fn upcast(self) -> LienSet {
        LienSet::default()
    }
}

impl<A> Upcast<LienSet> for Set<A>
where
    A: Upcast<Lien>,
    A: Ord,
{
    fn upcast(self) -> LienSet {
        LienSet {
            elements: self.upcast(),
        }
    }
}

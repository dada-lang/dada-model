use formality_core::{cast_impl, judgment_fn, set, Cons, Set, Upcast};

use crate::{
    grammar::{NamedTy, Parameter, Perm, Place, Predicate, Ty, UniversalVar},
    type_system::{places::place_ty, predicates::prove_predicate},
};

use super::env::Env;

#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum Lien {
    Copy,
    Lent,
    NoRead(Place),
    NoWrite(Place),
    Var(UniversalVar),
    NamedTy(NamedTy),
}

cast_impl!(Lien);
cast_impl!(Lien::Var(UniversalVar));
cast_impl!(Lien::NamedTy(NamedTy));

judgment_fn! {
    pub fn liens_from_parameter(
        env: Env,
        a: Parameter,
    ) => Set<Lien> {
        debug(a, env)

        (
            ----------------------------------- ("my")
            (liens_from_parameter(_env, Perm::My) => ())
        )

        (
            ----------------------------------- ("our")
            (liens_from_parameter(_env, Perm::Our) => set![Lien::Copy])
        )

        (
            (liens_from_places(env, places) => liens)
            ----------------------------------- ("shared")
            (liens_from_parameter(env, Perm::Shared(places)) => set![Lien::Copy, Lien::Lent, ..liens])
        )

        (
            (liens_from_places(env, places) => liens)
            ----------------------------------- ("leased")
            (liens_from_parameter(env, Perm::Leased(places)) => set![Lien::Lent, ..liens])
        )

        (
            (liens_from_places(env, places) => liens)
            ----------------------------------- ("given")
            (liens_from_parameter(env, Perm::Given(places)) => liens)
        )

        (
            ----------------------------------- ("universal var")
            (liens_from_parameter(_env, v: UniversalVar) => (v,))
        )

        (
            (liens_from_apply(env, &*l, &*r) => liens)
            ----------------------------------- ("perm-apply")
            (liens_from_parameter(env, Perm::Apply(l, r)) => liens)
        )

        (
            (liens_from_apply(env, l, &*r) => liens)
            ----------------------------------- ("ty-apply")
            (liens_from_parameter(env, Ty::ApplyPerm(l, r)) => liens)
        )

        (
            ----------------------------------- ("named ty")
            (liens_from_parameter(_env, Ty::NamedTy(n)) => set![Lien::NamedTy(n)])
        )

        (
            (liens_from_parameter(&env, &*l) => liens_l)
            (liens_from_parameter(&env, &*r) => liens_r)
            ----------------------------------- ("ty or")
            (liens_from_parameter(env, Ty::Or(l, r)) => Union(&liens_l, liens_r))
        )

        (
            (liens_from_parameter(&env, &*l) => liens_l)
            (liens_from_parameter(&env, &*r) => liens_r)
            ----------------------------------- ("perm or")
            (liens_from_parameter(env, Perm::Or(l, r)) => Union(&liens_l, liens_r))
        )

    }
}

judgment_fn! {
    fn liens_from_apply(
        env: Env,
        l: Parameter,
        r: Parameter,
    ) => Set<Lien> {
        debug(l, r, env)

        (
            (liens_from_parameter(&env, r) => liens)
            (&liens => l)
            (lien_is_copy(&env, l) => ())
            ----------------------------------- ("rhs is copy")
            (liens_from_apply(env, _l, r) => &liens)
        )

        (
            (liens_from_parameter(&env, l) => liens_l)
            (liens_from_parameter(&env, &r) => liens_r)
            ----------------------------------- ("rhs not copy")
            (liens_from_apply(env, l, r) => Union(&liens_l, liens_r))
        )
    }
}

judgment_fn! {
    fn liens_from_places(
        env: Env,
        places: Set<Place>,
    ) => Set<Lien> {
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
    ) => Set<Lien> {
        debug(place, env)

        (
            (place_ty(&env, &place) => ty)
            (liens_from_parameter(&env, ty) => liens)
            ----------------------------------- ("place")
            (liens_from_place(env, place) => liens)
        )
    }
}

judgment_fn! {
    fn lien_is_copy(
        env: Env,
        a: Lien,
    ) => () {
        debug(a, env)

        (
            ----------------------------------- ("copy")
            (lien_is_copy(_env, Lien::Copy) => ())
        )

        (
            (prove_predicate(env, Predicate::copy(v)) => ())
            ----------------------------------- ("var")
            (lien_is_copy(env, Lien::Var(v)) => ())
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
        let a: Set<C> = self.0.upcast();
        let b: Set<C> = self.1.upcast();
        set![..a, ..b]
    }
}

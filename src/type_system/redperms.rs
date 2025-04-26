use std::fmt::Debug;

use crate::{
    grammar::{ty_impls::PermTy, Parameter, Perm, Place, Variable},
    type_system::{
        predicates::{
            prove_is_lent, prove_is_my, prove_is_owned, prove_is_shared, prove_is_unique,
            prove_isnt_known_to_be_lent, prove_isnt_known_to_be_shared,
        },
        quantifiers::for_all,
        subperms::{sub_perms, sub_some_perm},
    },
};
use formality_core::{
    cast_impl, judgment_fn, Cons, Downcast, DowncastFrom, ProvenSet, Set, Upcast, UpcastFrom,
};

use super::{env::Env, liveness::LivePlaces};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct RedPerm {
    pub chains: Set<RedChain>,
}

cast_impl!(RedPerm);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct RedChain {
    pub links: Vec<RedLink>,
}

cast_impl!(RedChain);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum RedLink {
    Our,
    Rf(Place),
    Mt(Place),
    Mtd(Place),
    Mv(Place),
    Var(Variable),
}

cast_impl!(RedLink);

impl UpcastFrom<RedLink> for RedChain {
    fn upcast_from(term: RedLink) -> Self {
        RedChain { links: vec![term] }
    }
}

impl RedChain {
    pub fn my() -> Self {
        RedChain { links: vec![] }
    }
}

impl UpcastFrom<RedChain> for Parameter {
    fn upcast_from(term: RedChain) -> Self {
        let p: Perm = term.upcast();
        p.upcast()
    }
}

impl UpcastFrom<RedChain> for Perm {
    fn upcast_from(term: RedChain) -> Self {
        let mut links = term.links.into_iter();
        let Some(link0) = links.next() else {
            return Perm::My;
        };

        let perm0: Perm = link0.upcast();
        links.fold(perm0, |l, r| {
            let r: Perm = r.upcast();
            Perm::apply(l, r)
        })
    }
}

impl UpcastFrom<RedLink> for Parameter {
    fn upcast_from(term: RedLink) -> Self {
        let p: Perm = term.upcast();
        p.upcast()
    }
}

impl UpcastFrom<RedLink> for Perm {
    fn upcast_from(term: RedLink) -> Self {
        match term {
            RedLink::Our => Perm::Our,
            RedLink::Rf(place) => Perm::rf((place,)),
            RedLink::Mt(place) | RedLink::Mtd(place) => Perm::mt((place,)),
            RedLink::Mv(place) => Perm::mv((place,)),
            RedLink::Var(v) => Perm::var(v),
        }
    }
}

impl DowncastFrom<RedChain> for RedLink {
    fn downcast_from(t: &RedChain) -> Option<Self> {
        match t.links.len() {
            1 => Some(t.links[0].clone()),
            _ => None,
        }
    }
}

impl<T> DowncastFrom<RedChain> for Cons<RedLink, T>
where
    T: for<'a> DowncastFrom<&'a [RedLink]>,
{
    fn downcast_from(t: &RedChain) -> Option<Self> {
        let Some((link0, links)) = t.links.split_first() else {
            return None;
        };

        Some(Cons(link0.clone(), links.downcast()?))
    }
}

impl<T> UpcastFrom<Cons<RedLink, T>> for RedChain
where
    T: Upcast<RedChain>,
{
    fn upcast_from(Cons(head, tail): Cons<RedLink, T>) -> Self {
        let mut tail: RedChain = tail.upcast();
        tail.links.insert(0, head);
        tail
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct My();

impl UpcastFrom<My> for RedChain {
    fn upcast_from(_term: My) -> Self {
        RedChain { links: vec![] }
    }
}

impl DowncastFrom<RedChain> for My {
    fn downcast_from(t: &RedChain) -> Option<Self> {
        (&t.links[..]).downcast()
    }
}

impl DowncastFrom<&[RedLink]> for My {
    fn downcast_from(t: &&[RedLink]) -> Option<Self> {
        if t.len() == 0 {
            Some(My())
        } else {
            None
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Tail<T>(T);

impl DowncastFrom<&[RedLink]> for Tail<RedChain> {
    fn downcast_from(t: &&[RedLink]) -> Option<Self> {
        Some(Tail(RedChain {
            links: t.iter().cloned().collect(),
        }))
    }
}

judgment_fn! {
    /// Reduces `perm_a` and `perm_b` and then checks that `sub_perms` holds.
    pub fn sub_red_perms(
        env: Env,
        live_after: LivePlaces,
        perm_a: Perm,
        perm_b: Perm,
    ) => () {
        debug(perm_a, perm_b, live_after, env)

        (
            (red_perm(&env, &live_after, &perm_a) => red_perm_a)
            (red_perm(&env, &live_after, &perm_b) => red_perm_b)
            (for_all(&red_perm_a.chains, &|red_chain_a| {
                red_chain_sub_perm(&env, &live_after, &red_chain_a, &red_perm_b)
            }) => ())
            --- ("sub_red_perms")
            (sub_red_perms(env, live_after, perm_a, perm_b) => ())
        )
    }
}

judgment_fn! {
    /// Reduces `perm_a` and `perm_b` and then checks that `sub_perms` holds.
    pub fn red_chain_sub_perm(
        env: Env,
        live_after: LivePlaces,
        red_chain_a: RedChain,
        red_perm_b: RedPerm,
    ) => () {
        debug(red_chain_a, red_perm_b, live_after, env)

        (
            (red_perm_b.chains => red_chain_b)
            (red_chain_sub_chain(&env, &live_after, &red_chain_a, red_chain_b) => ())
            --- ("sub_red_perms")
            (red_chain_sub_perm(env, live_after, red_chain_a, red_perm_b) => ())
        )
    }
}

judgment_fn! {
    /// Reduces `perm_a` and `perm_b` and then checks that `sub_perms` holds.
    pub fn red_chain_sub_chain(
        env: Env,
        live_after: LivePlaces,
        red_chain_a: RedChain,
        red_chain_b: RedChain,
    ) => () {
        debug(red_chain_a, red_chain_b, live_after, env)

        (
            (prove_is_unique(&env, &link_a) => ())
            (prove_is_owned(&env, &link_a) => ())!
            (prove_is_unique(&env, &red_chain_b) => ())
            (prove_is_owned(&env, &red_chain_b) => ()) // FIXME: Is this truly needed?
            --- ("my <: unique")
            (red_chain_sub_chain(env, _live_after, link_a @ (RedLink::Our | RedLink::Var(_)), red_chain_b) => ())
        )

        (
            (prove_is_shared(&env, &link_a) => ())
            (prove_is_owned(&env, &link_a) => ())!
            (prove_is_shared(&env, &red_chain_b) => ())
            --- ("our <: shared")
            (red_chain_sub_chain(env, _live_after, link_a @ (RedLink::Our | RedLink::Var(_)), red_chain_b) => ())
        )

        (
            (prove_is_lent(&env, &tail_a) => ())
            (red_chain_sub_chain(&env, &live_after, &tail_a, &red_chain_b) => ())
            --- ("mut dead")
            (red_chain_sub_chain(env, live_after, Cons(RedLink::Mtd(_), Tail(tail_a)), red_chain_b) => ())
        )

        (
            (place_sub_place(&env, place_a, place_b) => ())
            (red_chain_sub_chain(&env, &live_after, &tail_a, &tail_b) => ())
            --- ("mut vs mut")
            (red_chain_sub_chain(
                env,
                live_after,
                Cons(RedLink::Mt(place_a), Tail(tail_a)),
                Cons(RedLink::Mt(place_b), Tail(tail_b)),
            ) => ())
        )

        (
            (place_sub_place(&env, place_a, place_b) => ())
            (red_chain_sub_chain(&env, &live_after, &tail_a, &tail_b) => ())
            --- ("ref vs ref")
            (red_chain_sub_chain(
                env,
                live_after,
                Cons(RedLink::Rf(place_a), Tail(tail_a)),
                Cons(RedLink::Rf(place_b), Tail(tail_b)),
            ) => ())
        )
    }
}

judgment_fn! {
    pub fn place_sub_place(
        env: Env,
        place_a: Place,
        place_b: Place,
    ) => () {
        debug(place_a, place_b, env)

        trivial(place_a == place_b => ())

        (
            (if place_b.is_prefix_of(&place_a))!
            (if let (Some((owner, _owner_ty)), field_ty) = env.owner_and_field_ty(&place_a)?)
            (let PermTy(field_perm, _) = field_ty.upcast())
            (prove_is_my(&env, &field_perm) => ())
            (place_sub_place(&env, &owner, &place_b) => ())
            --- ("prefix")
            (place_sub_place(env, place_a, place_b) => ())
        )

    }
}

judgment_fn! {
    /// Convert `perm` to a non-empty set of reduced permissions.
    /// Reduced permissions have a limited set of permissions:
    ///
    /// * `Perm::Our`.
    /// * `Perm::Ref[p]` where the type of `p` is not shared.
    /// * `Perm::Mut[p]` where either
    ///     * `p` is live
    ///     * `p` is dead and the type of `p` is not lent.
    /// * `Perm::Var(v)` is a variable `v`.
    /// * An applied permission `P Q` where `Q` is not shared.
    pub fn red_perm(
        env: Env,
        live_after: LivePlaces,
        perm: Perm,
    ) => RedPerm {
        debug(env, live_after, perm)

        (
            (collect(some_red_chain(&env, &live_after, perm)) => chains)
            --- ("collect")
            (red_perm(env, live_after, perm) => RedPerm { chains })
        )
    }
}

fn collect<P: Ord + Debug>(set: ProvenSet<P>) -> ProvenSet<Set<P>> {
    match set.into_set() {
        Ok(s) => ProvenSet::singleton(s),
        Err(e) => ProvenSet::from(*e),
    }
}

judgment_fn! {
    fn some_red_chain(
        env: Env,
        live_after: LivePlaces,
        perm: Perm,
    ) => RedChain {
        debug(perm, live_after, env)

        (
            --- ("my")
            (some_red_chain(_env, _live_after, Perm::My) => My)
        )

        (
            --- ("our")
            (some_red_chain(_env, _live_after, Perm::Our) => RedLink::Our)
        )

        (
            --- ("var")
            (some_red_chain(_env, _live_after, Perm::Var(v)) => RedLink::Var(v))
        )

        (
            (places => place)
            --- ("moved")
            (some_red_chain(_env, live_after, Perm::Mv(places)) => RedLink::Mv(place))
        )

        (
            (places => place)
            --- ("ref")
            (some_red_chain(_env, live_after, Perm::Rf(places)) => RedLink::Rf(place))
        )

        (
            (places => place)
            (if !live_after.is_live(&place))
            --- ("mut")
            (some_red_chain(_env, live_after, Perm::Rf(places)) => RedLink::Mtd(place))
        )
        (
            (places => place)
            (if live_after.is_live(&place))
            --- ("mut")
            (some_red_chain(_env, live_after, Perm::Rf(places)) => RedLink::Mt(place))
        )

        (
            (some_red_chain(&env, &live_after, &*perm1) => red_chain)
            (prove_is_shared(&env, &red_chain) => ())
            --- ("apply to shared")
            (some_red_chain(env, live_after, Perm::Apply(_perm0, perm1)) => &red_chain)
        )

        (
            (some_red_chain(&env, &live_after, &*perm0) => red_chain0)
            (some_red_chain(&env, &live_after, &*perm1) => red_chain1)
            (prove_isnt_known_to_be_shared(&env, &red_chain1) => ())
            --- ("apply to !shared")
            (some_red_chain(env, live_after, Perm::Apply(perm0, perm1)) => RedChain {
                links: red_chain0.links.iter().chain(&red_chain1.links).cloned().collect()
            })
        )
    }
}

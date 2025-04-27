use std::fmt::Debug;

use crate::{
    grammar::{ty_impls::PermTy, Perm, Place, Variable},
    type_system::{
        predicates::{
            prove_is_lent, prove_is_my, prove_is_our, prove_is_shareable, prove_is_shared,
            prove_isnt_known_to_be_shared,
        },
        quantifiers::for_all,
    },
};
use formality_core::{cast_impl, judgment_fn, ProvenSet, Set, Upcast};

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
    Rfl(Place),
    Rfd(Place),
    Mtl(Place),
    Mtd(Place),
    Mv(Place),
    Var(Variable),
}

mod cast_impls;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct My();

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Head<H, T>(H, T);

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Tail<T>(T);

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
            (prove_is_my(&env, &red_chain_a) => ())!
            (prove_is_my(&env, &red_chain_b) => ()) // could this be 'prove unique'?
            --- ("my <: unique")
            (red_chain_sub_chain(env, _live_after, red_chain_a, red_chain_b) => ())
        )

        (
            (prove_is_our(&env, &link_a) => ())
            (prove_is_shared(&env, &red_chain_b) => ())
            --- ("our <: shared")
            (red_chain_sub_chain(env, _live_after, link_a @ (RedLink::Our | RedLink::Var(_)), red_chain_b) => ())
        )

        (
            (let ty_dead = env.place_ty(&place_dead)?)
            (prove_is_shareable(&env, &ty_dead) => ())
            (prove_is_lent(&env, &tail_a) => ())
            (red_chain_sub_chain(&env, &live_after, &tail_a, &red_chain_b) => ())
            --- ("mut dead")
            (red_chain_sub_chain(env, live_after, Head(RedLink::Mtd(place_dead), Tail(tail_a)), red_chain_b) => ())
        )

        (
            (let ty_dead = env.place_ty(&place_dead)?)
            (prove_is_shareable(&env, &ty_dead) => ())
            (prove_is_lent(&env, &tail_a) => ())
            (red_chain_sub_chain(&env, &live_after, Head(RedLink::Our, Tail(&tail_a)), &red_chain_b) => ())
            --- ("ref dead")
            (red_chain_sub_chain(env, live_after, Head(RedLink::Rfd(place_dead), Tail(tail_a)), red_chain_b) => ())
        )

        (
            (place_sub_place(&env, place_a, place_b) => ())
            (red_chain_sub_chain(&env, &live_after, &tail_a, &tail_b) => ())
            --- ("mut vs mut")
            (red_chain_sub_chain(
                env,
                live_after,
                Head(RedLink::Mtl(place_a) | RedLink::Mtd(place_a), Tail(tail_a)),
                Head(RedLink::Mtl(place_b) | RedLink::Mtd(place_b), Tail(tail_b)),
            ) => ())
        )

        (
            (place_sub_place(&env, place_a, place_b) => ())
            (red_chain_sub_chain(&env, &live_after, &tail_a, &tail_b) => ())
            --- ("ref vs ref")
            (red_chain_sub_chain(
                env,
                live_after,
                Head(RedLink::Rfl(place_a) | RedLink::Rfd(place_a), Tail(tail_a)),
                Head(RedLink::Rfl(place_b) | RedLink::Rfd(place_b), Tail(tail_b)),
            ) => ())
        )

        (
            (place_sub_place(&env, place_a, place_b) => ())
            (red_chain_sub_chain(&env, &live_after, &tail_a, &tail_b) => ())
            --- ("ref vs our mut")
            (red_chain_sub_chain(
                env,
                live_after,
                Head(RedLink::Rfl(place_a) | RedLink::Rfd(place_a), Tail(tail_a)),
                Head(RedLink::Our, Head(RedLink::Mtl(place_b) | RedLink::Mtd(place_b), Tail(tail_b))),
            ) => ())
        )

        (
            (prove_is_our(&env, link_a) => ())
            (prove_is_shared(&env, &link_b) => ())
            (red_chain_sub_chain(&env, &live_after, &tail_a, &tail_b) => ())
            --- ("our vs shared")
            (red_chain_sub_chain(
                env,
                live_after,
                Head(link_a, Tail(tail_a)),
                Head(link_b, Tail(tail_b)),
            ) => ())
        )

        (
            (if v_a == v_b)!
            (red_chain_sub_chain(&env, &live_after, &tail_a, &tail_b) => ())
            --- ("var vs var")
            (red_chain_sub_chain(
                env,
                live_after,
                Head(RedLink::Var(v_a), Tail(tail_a)),
                Head(RedLink::Var(v_b), Tail(tail_b)),
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
            (collect(some_expanded_red_chain(&env, &live_after, perm)) => chains)
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

fn tail_link(chain: &RedChain) -> Option<RedLink> {
    let link = chain.links.last()?;
    Some(link.clone())
}

fn pop_link(chain: impl Upcast<RedChain>) -> Option<(RedChain, RedLink)> {
    let mut chain: RedChain = chain.upcast();
    let link = chain.links.pop()?;
    Some((chain, link))
}

judgment_fn! {
    fn some_expanded_red_chain(
        env: Env,
        live_after: LivePlaces,
        perm: Perm,
    ) => RedChain {
        debug(perm, live_after, env)

        (
            (some_red_chain(env, live_after, perm) => red_chain)
            (if let None | Some(RedLink::Our) | Some(RedLink::Var(_)) = tail_link(&red_chain))
            --- ("inextensible")
            (some_expanded_red_chain(env, live_after, perm) => red_chain)
        )

        (
            (some_red_chain(&env, &live_after, perm) => red_chain)
            (if let Some(RedLink::Mtl(place) | RedLink::Mtd(place) | RedLink::Rfl(place) | RedLink::Rfd(place)) = tail_link(&red_chain))
            (if let PermTy(Perm::My, _) = env.place_ty(&place)?.upcast())
            --- ("(mut | ref) from my")
            (some_expanded_red_chain(env, live_after, perm) => red_chain)
        )

        (
            (some_red_chain(&env, &live_after, perm) => red_chain)
            (if let Some(RedLink::Mtl(place) | RedLink::Mtd(place) | RedLink::Rfl(place) | RedLink::Rfd(place)) = tail_link(&red_chain))
            (let PermTy(perm_place, _) = env.place_ty(&place)?.upcast())
            (some_red_chain(&env, &live_after, perm_place) => red_chain_place)
            (append_chain(&env, &red_chain, red_chain_place) => red_chain_out)

            // subtle: if `perm_place` is `Perm::My`, this will recurse and fail with a cycle
            (some_expanded_red_chain(&env, &live_after, red_chain_out) => red_chain_out)
            --- ("(mut | ref) from non-my")
            (some_expanded_red_chain(env, live_after, perm) => red_chain_out)
        )

        (
            (some_red_chain(&env, &live_after, perm) => red_chain)
            (if let Some((red_chain_head, RedLink::Mv(place))) = pop_link(&red_chain))
            (let PermTy(perm_place, _) = env.place_ty(&place)?.upcast())
            (some_red_chain(&env, &live_after, perm_place) => red_chain_place)
            (append_chain(&env, &red_chain_head, red_chain_place) => red_chain_out)
            (some_expanded_red_chain(&env, &live_after, red_chain_out) => red_chain_out)
            --- ("mv")
            (some_expanded_red_chain(env, live_after, perm) => red_chain_out)
        )
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
            (some_red_chain(_env, _live_after, Perm::My) => My())
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
            (some_red_chain(_env, _live_after, Perm::Mv(places)) => RedLink::Mv(place))
        )

        (
            (places => place)
            (if !live_after.is_live(&place))
            --- ("ref")
            (some_red_chain(_env, _live_after, Perm::Rf(places)) => RedLink::Rfd(place))
        )

        (
            (places => place)
            (if live_after.is_live(&place))
            --- ("ref")
            (some_red_chain(_env, _live_after, Perm::Rf(places)) => RedLink::Rfl(place))
        )

        (
            (places => place)
            (if !live_after.is_live(&place))
            --- ("mut")
            (some_red_chain(_env, live_after, Perm::Mt(places)) => RedLink::Mtd(place))
        )
        (
            (places => place)
            (if live_after.is_live(&place))
            --- ("mut")
            (some_red_chain(_env, live_after, Perm::Mt(places)) => RedLink::Mtl(place))
        )

        (
            (some_red_chain(&env, &live_after, &*perm0) => red_chain0)
            (some_red_chain(&env, &live_after, &*perm1) => red_chain1)
            (append_chain(&env, &red_chain0, red_chain1) => red_chain)
            --- ("apply")
            (some_red_chain(env, live_after, Perm::Apply(perm0, perm1)) => red_chain)
        )
    }
}

judgment_fn! {
    fn append_chain(
        env: Env,
        lhs: RedChain,
        rhs: RedChain,
    ) => RedChain {
        debug(lhs, rhs, env)

        (
            (prove_is_shared(&env, &rhs) => ())
            --- ("apply to shared")
            (append_chain(env, _lhs, rhs) => &rhs)
        )

        (
            (prove_isnt_known_to_be_shared(&env, &rhs) => ())
            (let links = lhs.links.iter().chain(&rhs.links).cloned().collect())
            --- ("apply to !shared")
            (append_chain(env, lhs, rhs) => RedChain { links })
        )
    }
}

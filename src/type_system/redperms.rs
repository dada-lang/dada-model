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
    pub fn sub_perms(
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
                red_chain_sub_perm(&env, &red_chain_a, &red_perm_b)
            }) => ())
            --- ("sub_red_perms")
            (sub_perms(env, live_after, perm_a, perm_b) => ())
        )
    }
}

judgment_fn! {
    /// Reduces `perm_a` and `perm_b` and then checks that `sub_perms` holds.
    pub fn red_chain_sub_perm(
        env: Env,
        red_chain_a: RedChain,
        red_perm_b: RedPerm,
    ) => () {
        debug(red_chain_a, red_perm_b, env)

        (
            (red_perm_b.chains => red_chain_b)
            (red_chain_sub_chain(&env, &red_chain_a, red_chain_b) => ())
            --- ("sub_red_perms")
            (red_chain_sub_perm(env, red_chain_a, red_perm_b) => ())
        )
    }
}

judgment_fn! {
    /// Reduces `perm_a` and `perm_b` and then checks that `sub_perms` holds.
    pub fn red_chain_sub_chain(
        env: Env,
        red_chain_a: RedChain,
        red_chain_b: RedChain,
    ) => () {
        debug(red_chain_a, red_chain_b, env)

        (
            (prove_is_my(&env, &red_chain_a) => ())!

            // NB: This cannot be `prove_unique` because of guard classes and the like.
            // A `my Guard` is not `share`, but `mut[g] Guard` is.
            // If `my <: mut[g]`, then `my Guard <: mut[g] Guard`, but the upcasting
            // would make `share(my Guard)` have to hold, which would make guard classes
            // unsound.
            (prove_is_my(&env, &red_chain_b) => ())
            --- ("(my) vs (my)")
            (red_chain_sub_chain(env, red_chain_a, red_chain_b) => ())
        )

        (
            (prove_is_our(&env, &link_a) => ())
            (prove_is_shared(&env, &red_chain_b) => ())
            --- ("(our) vs (shared)")
            (red_chain_sub_chain(env, link_a @ (RedLink::Our | RedLink::Var(_)), red_chain_b) => ())
        )

        (
            (prove_is_our(&env, link_a) => ())
            (prove_is_shared(&env, &link_b) => ())
            (red_chain_sub_chain(&env, &tail_a, &tail_b) => ())
            --- ("(our::P) vs (shared::P)")
            (red_chain_sub_chain(
                env,
                Head(link_a, Tail(tail_a)),
                Head(link_b, Tail(tail_b)),
            ) => ())
        )

        (
            // NB: We can only drop a `mut[g]` if `share(G)` (where `g: G`).
            // This accounts for the possibility of custom destructors on guard classes.
            (let ty_dead = env.place_ty(&place_dead)?)
            (prove_is_shareable(&env, &ty_dead) => ())
            (prove_is_lent(&env, &tail_a) => ())
            (red_chain_sub_chain(&env, &tail_a, &red_chain_b) => ())
            --- ("(mut-dead::P) vs Q ~~> (P) vs Q")
            (red_chain_sub_chain(env, Head(RedLink::Mtd(place_dead), Tail(tail_a)), red_chain_b) => ())
        )

        (
            // NB: We can only convert a `ref[g]` to `our` if `share(g)`.
            // This accounts for the possibility of custom destructors on guard classes.
            (let ty_dead = env.place_ty(&place_dead)?)
            (prove_is_shareable(&env, &ty_dead) => ())
            (prove_is_lent(&env, &tail_a) => ())
            (red_chain_sub_chain(&env, Head(RedLink::Our, Tail(&tail_a)), &red_chain_b) => ())
            --- ("(ref-dead::P) vs Q ~~> (our::P) vs Q")
            (red_chain_sub_chain(env, Head(RedLink::Rfd(place_dead), Tail(tail_a)), red_chain_b) => ())
        )

        (
            (if place_b.is_prefix_of(&place_a))
            (red_chain_sub_chain(&env, &tail_a, &tail_b) => ())
            --- ("(mut::P) vs (mut::P)")
            (red_chain_sub_chain(
                env,
                Head(RedLink::Mtl(place_a) | RedLink::Mtd(place_a), Tail(tail_a)),
                Head(RedLink::Mtl(place_b) | RedLink::Mtd(place_b), Tail(tail_b)),
            ) => ())
        )

        (
            (if place_b.is_prefix_of(&place_a))
            (red_chain_sub_chain(&env, &tail_a, &tail_b) => ())
            --- ("(ref::P) vs (ref::P)")
            (red_chain_sub_chain(
                env,
                Head(RedLink::Rfl(place_a) | RedLink::Rfd(place_a), Tail(tail_a)),
                Head(RedLink::Rfl(place_b) | RedLink::Rfd(place_b), Tail(tail_b)),
            ) => ())
        )

        (
            (if place_b.is_prefix_of(&place_a))
            (red_chain_sub_chain(&env, &tail_a, &tail_b) => ())
            --- ("(ref::P) vs (our::mut::P)")
            (red_chain_sub_chain(
                env,
                Head(RedLink::Rfl(place_a) | RedLink::Rfd(place_a), Tail(tail_a)),
                Head(RedLink::Our, Head(RedLink::Mtl(place_b) | RedLink::Mtd(place_b), Tail(tail_b))),
            ) => ())
        )

        (
            (if v_a == v_b)!
            (red_chain_sub_chain(&env, &tail_a, &tail_b) => ())
            --- ("(var::P) vs (var::P)")
            (red_chain_sub_chain(
                env,
                Head(RedLink::Var(v_a), Tail(tail_a)),
                Head(RedLink::Var(v_b), Tail(tail_b)),
            ) => ())
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

// Hack to leverage the search functionality of formality-core.
// Collect all `P` that were provable and create a set `P`.
// The judgments used to create `set` are not being used in the usual
// way, they must be both SOUND *and* COMPLETE.
//
// I use the name prefix `some_` to denote that (they are resulting in
// *some* red chain, not *all* red chains).
fn collect<P: Ord + Debug>(set: ProvenSet<P>) -> ProvenSet<Set<P>> {
    match set.into_set() {
        Ok(s) => ProvenSet::singleton(s),
        Err(e) => ProvenSet::from(*e),
    }
}

/// Yield the final link in the chain (None for empty chains).
fn tail_link(chain: &RedChain) -> Option<RedLink> {
    let link = chain.links.last()?;
    Some(link.clone())
}

/// Yield the final link in the chain and the chain prefix (None for empty chains)
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

        // If the chain ends in `our` or `var`, cannot expand it.
        (
            (some_red_chain(env, live_after, perm) => red_chain)
            (if let None | Some(RedLink::Our) | Some(RedLink::Var(_)) = tail_link(&red_chain))
            --- ("inextensible")
            (some_expanded_red_chain(env, live_after, perm) => red_chain)
        )

        // If the chain ends in `ref[p]` or `mut[p]`, and the type of `p` is `my`,
        // cannot expand it.
        (
            (some_red_chain(&env, &live_after, perm) => red_chain)
            (if let Some(
                RedLink::Mtl(place) | RedLink::Mtd(place) |
                RedLink::Rfl(place) | RedLink::Rfd(place)
            ) = tail_link(&red_chain))
            (if let PermTy(Perm::My, _) = env.place_ty(&place)?.upcast())
            --- ("(mut | ref) from my")
            (some_expanded_red_chain(env, live_after, perm) => red_chain)
        )

        // If the chain ends in `ref[p]` or `mut[p]`,
        // we can extend it with the permission from `p`.
        (
            (some_red_chain(&env, &live_after, perm) => red_chain)
            (if let Some(
                RedLink::Mtl(place) | RedLink::Mtd(place) |
                RedLink::Rfl(place) | RedLink::Rfd(place)
            ) = tail_link(&red_chain))
            (let PermTy(perm_place, _) = env.place_ty(&place)?.upcast())
            (some_red_chain(&env, &live_after, perm_place) => red_chain_place)
            (append_chain(&env, &red_chain, red_chain_place) => red_chain_out)

            // subtle: if `perm_place` is `Perm::My`, this will recurse and fail with a cycle
            (some_expanded_red_chain(&env, &live_after, red_chain_out) => red_chain_out)
            --- ("(mut | ref) from non-my")
            (some_expanded_red_chain(env, live_after, perm) => red_chain_out)
        )

        // If the chain ends in `move[p]`, we can *replace* it with the permission from `p`.
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

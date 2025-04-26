use std::fmt::Debug;

use crate::{
    grammar::{ty_impls::PermTy, Perm},
    type_system::{
        predicates::{
            prove_is_lent, prove_is_shared, prove_isnt_known_to_be_lent,
            prove_isnt_known_to_be_shared,
        },
        quantifiers::for_all,
        subperms::{sub_perms, sub_some_perm},
    },
};
use formality_core::{judgment_fn, ProvenSet, Set, Upcast};

use super::{env::Env, liveness::LivePlaces};

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
            (red_perms(&env, &live_after, &perm_a) => perm_reds_a)
            (red_perms(&env, &live_after, &perm_b) => perm_reds_b)
            (let () = {
                eprintln!("perm_reds_a: {perm_reds_a:?}");
                eprintln!("perm_reds_b: {perm_reds_b:?}");
            })
            (for_all(&perm_reds_a, &|perm_red_a| {
                eprintln!("perm_red_a: {perm_red_a:?}");
                sub_some_perm(&env, &live_after, &perm_red_a, &perm_reds_b)
            }) => ())
            --- ("sub_red_perms")
            (sub_red_perms(env, live_after, perm_a, perm_b) => ())
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
    pub fn red_perms(
        env: Env,
        live_after: LivePlaces,
        perm: Perm,
    ) => Set<Perm> {
        debug(env, live_after, perm)

        (
            (collect(some_expanded_red_perm(&env, &live_after, perm)) => perms_red)
            --- ("collect")
            (red_perms(env, live_after, perm) => perms_red)
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
    fn some_expanded_red_perm(
        env: Env,
        live_after: LivePlaces,
        perm: Perm,
    ) => Perm {
        debug(perm, live_after, env)

        (
            (some_red_perm(env, live_after, perm) => perm_red)
            (if let Perm::My | Perm::Our | Perm::Var(_) = tail(&perm_red))
            --- ("my | our | var")
            (some_expanded_red_perm(env, live_after, perm) => &perm_red)
        )

        (
            (some_red_perm(env, live_after, perm) => perm_red)
            (if let Perm::Rf(_) | Perm::Mt(_) = tail(&perm_red))
            --- ("ref | mut")
            (some_expanded_red_perm(env, live_after, perm) => &perm_red)
        )
    }
}

judgment_fn! {
    fn some_red_perm(
        env: Env,
        live_after: LivePlaces,
        perm: Perm,
    ) => Perm {
        debug(perm, live_after, env)

        (
            --- ("my")
            (some_red_perm(_env, _live_after, Perm::My) => Perm::My)
        )

        (
            --- ("our")
            (some_red_perm(_env, _live_after, Perm::Our) => Perm::Our)
        )

        (
            --- ("var")
            (some_red_perm(_env, _live_after, Perm::Var(v)) => Perm::Var(v))
        )

        (
            (places => place)
            (let PermTy(perm, _) = env.place_ty(&place)?.upcast())
            (some_red_perm(&env, &live_after, &perm) => perm_red)
            --- ("moved")
            (some_red_perm(env, live_after, Perm::Mv(places)) => perm_red)
        )

        (
            (places => place)
            (let PermTy(perm, _) = env.place_ty(&place)?.upcast())
            (prove_is_shared(&env, &perm) => ())
            (some_red_perm(&env, &live_after, &perm) => perm_red)
            --- ("ref, shared")
            (some_red_perm(env, live_after, Perm::Rf(places)) => perm_red)
        )

        (
            (places => place)
            (let PermTy(perm, _) = env.place_ty(&place)?.upcast())
            (prove_isnt_known_to_be_shared(&env, &perm) => ())
            --- ("ref, !shared")
            (some_red_perm(env, _live_after, Perm::Rf(places)) => Perm::rf((&place,)))
        )

        (
            (places => place)
            (let PermTy(perm, _) = env.place_ty(&place)?.upcast())
            (prove_is_shared(&env, &perm) => ())
            (some_red_perm(&env, &live_after, &perm) => perm_red)
            --- ("mut, shared")
            (some_red_perm(env, live_after, Perm::Mt(places)) => perm_red)
        )

        (
            (places => place)
            (if !live_after.is_live(&place))
            (let PermTy(perm, _) = env.place_ty(&place)?.upcast())
            (prove_is_lent(&env, &perm) => ())
            (some_red_perm(&env, &live_after, &perm) => perm_red)
            --- ("mut, dead and lent")
            (some_red_perm(env, live_after, Perm::Mt(places)) => perm_red)
        )

        (
            (places => place)
            (let PermTy(perm, _) = env.place_ty(&place)?.upcast())
            (prove_isnt_known_to_be_lent(&env, &perm) => ())
            (prove_isnt_known_to_be_shared(&env, &perm) => ())
            --- ("mut, !lent && !shared")
            (some_red_perm(env, _live_after, Perm::Mt(places)) => Perm::mt((&place,)))
        )

        (
            (places => place)
            (if live_after.is_live(&place))
            (let PermTy(perm, _) = env.place_ty(&place)?.upcast())
            (prove_isnt_known_to_be_shared(&env, &perm) => ())
            --- ("mut, live && !shared")
            (some_red_perm(env, live_after, Perm::Mt(places)) => Perm::mt((&place,)))
        )

        (
            (some_red_perm(&env, &live_after, &*perm1) => perm_red1)
            (prove_is_shared(&env, &perm_red1) => ())
            --- ("apply to shared")
            (some_red_perm(env, live_after, Perm::Apply(_perm0, perm1)) => &perm_red1)
        )

        (
            (some_red_perm(&env, &live_after, &*perm0) => perm_red0)
            (some_red_perm(&env, &live_after, &*perm1) => perm_red1)
            (prove_isnt_known_to_be_shared(&env, &perm_red1) => ())
            --- ("apply to !shared")
            (some_red_perm(env, live_after, Perm::Apply(perm0, perm1)) => Perm::apply(&perm_red0, &perm_red1))
        )
    }
}

fn tail(perm: &Perm) -> &Perm {
    if let Perm::Apply(_, perm1) = perm {
        tail(perm1)
    } else {
        perm
    }
}

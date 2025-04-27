use formality_core::{judgment_fn, Set, Upcast};

use crate::{
    grammar::{ty_impls::PermTy, Perm, Place},
    type_system::{
        env::Env,
        liveness::LivePlaces,
        predicates::{
            prove_is_lent, prove_is_owned, prove_is_shareable, prove_is_shared, prove_is_unique,
        },
        quantifiers::for_all,
    },
};

use crate::type_system::perm_matcher::{Head, Leaf, Tail};

use super::perm_matcher::Access;

judgment_fn! {
    pub fn sub_some_perm(
        env: Env,
        live_after: LivePlaces,
        a: Perm,
        bs: Set<Perm>,
    ) => () {
        debug(a, bs, live_after, env)

        trivial(bs.contains(&a) => ())

        (
            (bs => b)
            (sub_perms(&env, &live_after, &a, &b) => ())
            ------------------------------- ("apply to shared, left")
            (sub_some_perm(env, live_after, a, bs) => ())
        )

    }
}

judgment_fn! {
    pub fn sub_perms(
        env: Env,
        live_after: LivePlaces,
        a: Perm,
        b: Perm,
    ) => () {
        debug(a, b, live_after, env)

        trivial(a == b => ())

        // SHARED RULES
        //
        // Applying a perm L to a shared perm R just yields R.
        // This can occur either as an apply (e.g., `mut[p] ref[q]` is just `ref[q]`)
        // or via a place (e.g., `mut[p]` where `p: ref[q] String` is just `ref[q]`).

        (
            (prove_is_shared(&env, &tail_a) => ())
            (sub_perms(&env, &live_after, &tail_a, &perm_b) => ())
            ------------------------------- ("apply to shared, left")
            (sub_perms(env, live_after, Head(_, tail_a @ Head(Leaf::Our | Leaf::Place(..) | Leaf::Places(..) | Leaf::Var(_), Tail(_))), perm_b) => ())
        )

        (
            (prove_is_shared(&env, &tail_b) => ())
            (sub_perms(&env, &live_after, &perm_a, &tail_b) => ())
            ------------------------------- ("apply to shared, right")
            (sub_perms(env, live_after, perm_a, Head(_, tail_b @ Head(Leaf::Our | Leaf::Place(..) | Leaf::Places(..) | Leaf::Var(_), Tail(_)))) => ())
        )

        // (
        //     (any_place(&env, &place) => PermTy(head_a, _))
        //     (prove_is_shared(&env, &head_a) => ())
        //     (sub_perms(&env, &live_after, Head(&head_a, Tail(&tail_a)), &perm_b) => ())
        //     ------------------------------- ("access shared left")
        //     (sub_perms(env, live_after, Head(Leaf::Place(_, place), Tail(tail_a)), perm_b) => ())
        // )

        // (
        //     (any_place(&env, &place) => PermTy(head_b, _))
        //     (prove_is_shared(&env, &head_b) => ())
        //     (sub_perms(&env, &live_after, &perm_a, Head(&head_b, Tail(&tail_b))) => ())
        //     ------------------------------- ("access shared right")
        //     (sub_perms(env, live_after, perm_a, Head(Leaf::Place(_, place), Tail(tail_b))) => ())
        // )

        // FLATTEN RULES
        //
        // When a permission represents multiple alternatives (e.g., `ref[p, q]`)
        // then it can be converted to those alternatives (e.g., `ref[a], ref[b]`)
        // and either for-all or there-exists depending on where the perm appears.

        (
            (for_all(places, &|place| sub_perms(&env, &live_after, Head(Leaf::place(acc, place), Tail(&tail_a)), &perm_b)) => ())
            ------------------------------- ("flatten left")
            (sub_perms(env, live_after, Head(Leaf::Places(acc, places), Tail(tail_a)), perm_b) => ())
        )

        (
            (places => place)
            (sub_perms(&env, &live_after, &perm_a, Head(Leaf::Place(acc, place), Tail(&tail_b))) => ())
            ------------------------------- ("flatten right")
            (sub_perms(env, live_after, perm_a, Head(Leaf::Places(acc, places), Tail(tail_b))) => ())
        )

        // DEAD RULES
        //
        // When the final permission in the list is an access to a dead place
        // (e.g. `ref[p]`) and the place has a suitable perm (e.g., `p: ref[q] Ty`),
        // then the final perm can be dropped (e.g., resulting in `ref[q]`).

        (
            (if !live_after.is_live(place))!
            (dead_perm(&env, &live_after, acc, place, tail_a) => perm_a)
            (sub_perms(&env, &live_after, perm_a, &perm_b) => ())
            ------------------------------- ("dead left")
            (sub_perms(env, live_after, Head(Leaf::Place(acc, place), Tail(tail_a)), perm_b) => ())
        )

        // NB. There is no "dead right" rule -- just because a
        // variable is dead doesn't let you ignore that part of
        // the supertype. This would let you do surprising things
        // like store from `mut[d1]` into `mut[d2]` just because
        // `d2` is dead. See test `liskov_from_pair_leased_with_pair_dead`.
        //
        // (
        //     (if !live_after.is_live(place))!
        //     (dead_perm(&env, &live_after, acc, place) => head_b)
        //     (sub_perms(&env, &live_after, &perm_a, head_b.apply_to(&tail_b)) => ())
        //     ------------------------------- ("dead right")
        //     (sub_perms(env, live_after, perm_a, Head(Leaf::Place(acc, place), Tail(tail_b))) => ())
        // )

        // EXPANSION RULES
        //
        // When the final permission in the list is an access (e.g., `ref[p]`)
        // expand it to have the permission from `p` (e.g., `p: ref[q] Ty`)
        // then this permission can be expanded (e.g., resulting in `ref[p] ref[q]`).

        (
            (expand_perm(&env, acc, place) => perm_a)!
            (sub_perms(&env, &live_after, perm_a, &perm_b) => ())
            ------------------------------- ("expand left")
            (sub_perms(env, live_after, Leaf::Place(acc, place), perm_b) => ())
        )

        (
            (expand_perm(&env, acc, place) => perm_b)!
            (sub_perms(&env, &live_after, &perm_a, perm_b) => ())
            ------------------------------- ("expand right")
            (sub_perms(env, live_after, perm_a, Leaf::Place(acc, place)) => ())
        )

        // POP FIELD

        (
            (if let (Some((owner, _owner_ty)), field_ty) = env.owner_and_field_ty(&place)?)!
            (let PermTy(field_perm, _) = field_ty.upcast())
            (prove_is_owned(&env, &field_perm) => ())
            (prove_is_unique(&env, &field_perm) => ())
            (sub_perms(&env, &live_after, Head(Leaf::place(&acc, &owner), &tail_a), &perm_b) => ())
            ------------------------------- ("pop field")
            (sub_perms(env, live_after, Head(Leaf::Place(acc, place), Tail(tail_a)), perm_b) => ())
        )

        // MATCH RULES
        //
        // Match equivalent permissions from the front of the list.

        (
            (if head_a == head_b)!
            (sub_perms(env, live_after, tail_a, tail_b) => ())
            ------------------------------- ("match heads")
            (sub_perms(env, live_after, Head(head_a, Tail(tail_a)), Head(head_b, Tail(tail_b))) => ())
        )

        (
            (if place_r == place_m)!
            (sub_perms(&env, &live_after, &tail_a, &tail_b) => ())
            ------------------------------- ("ref <= our mut")
            (sub_perms(env, live_after,
                Head(Leaf::Place(Access::Rf, place_r), Tail(tail_a)),
                Head(Leaf::Our, Head(Leaf::Place(Access::Mt, place_m), Tail(tail_b))),
            ) => ())
        )

        // MY and OUR

        (
            (prove_is_shared(&env, &head_a) => ())
            (prove_is_owned(&env, &head_a) => ())!
            (prove_is_shared(&env, &head_b) => ())
            (sub_perms(&env, &live_after, &tail_a, &tail_b) => ())
            ------------------------------- ("our left")
            (sub_perms(env, live_after, Head(head_a, Tail(tail_a)), Head(head_b, Tail(tail_b))) => ())
        )

        (
            (prove_is_shared(&env, &perm_a) => ())
            (prove_is_owned(&env, &perm_a) => ())!
            (prove_is_shared(&env, &perm_b) => ())
            ------------------------------- ("our left")
            (sub_perms(env, _live_after, perm_a @ (Leaf::Our | Leaf::Var(_)), perm_b) => ())
        )

        (
            (prove_is_unique(&env, &perm_a) => ())
            (prove_is_owned(&env, &perm_a) => ())!
            (prove_is_unique(&env, &perm_b) => ())
            (prove_is_owned(&env, &perm_b) => ())
            ------------------------------- ("my left")
            (sub_perms(env, _live_after, perm_a @ (Leaf::My | Leaf::Var(_)), perm_b) => ())
        )
    }
}

judgment_fn! {
    fn expand_perm(
        env: Env,
        acc: Access,
        place: Place,
    ) => Perm {
        debug(acc, place, env)

        (
            (let PermTy(perm_a, _) = env.place_ty(&place_a)?.upcast())
            ------------------------------- ("expand ref")
            (expand_perm(env, Access::Rf, place_a) => Head(Perm::rf((place_a,)), Tail(&perm_a)))
        )

        (
            (let PermTy(perm_a, _) = env.place_ty(&place_a)?.upcast())
            ------------------------------- ("expand mut")
            (expand_perm(env, Access::Mt, place_a) => Head(Perm::mt((&place_a,)), Tail(&perm_a)))
        )

        (
            (let PermTy(perm_a, _) = env.place_ty(&place_a)?.upcast())
            ------------------------------- ("expand move")
            (expand_perm(env, Access::Mv, place_a) => perm_a)
        )
    }
}

judgment_fn! {
    fn dead_perm(
        env: Env,
        live_after: LivePlaces,
        acc: Access,
        place: Place,
        tail: Perm,
    ) => Perm {
        debug(acc, place, tail, live_after, env)

        (
            (if !live_after.is_live(&place_dead))!
            (let ty_dead = env.place_ty(&place_dead)?)
            (prove_is_shareable(&env, &ty_dead) => ())
            (prove_is_lent(&env, &tail) => ())
            ------------------------------- ("dead ref")
            (dead_perm(env, live_after, Access::Rf, place_dead, tail) => Head(Perm::Our, Tail(&tail)))
        )

        (
            (if !live_after.is_live(&place_dead))!
            (let ty_dead = env.place_ty(&place_dead)?)
            (prove_is_shareable(&env, &ty_dead) => ())
            (prove_is_lent(&env, &tail) => ())
            ------------------------------- ("dead mut")
            (dead_perm(env, live_after, Access::Mt, place_dead, tail) => &tail)
        )
    }
}

judgment_fn! {
    fn any_place(
        env: Env,
        place: Place,
    ) => PermTy {
        debug(env, place)

        (
            (let ty = env.place_ty(&place)?)
            ------------------------------- ("any_place")
            (any_place(env, place) => ty)
        )
    }
}

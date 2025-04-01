use formality_core::{judgment_fn, Cons, Set};

use crate::{
    grammar::{perm_impls::LeafPerms, Perm, Place},
    type_system::{
        env::Env,
        liveness::LivePlaces,
        predicates::{prove_is_copy, prove_is_lent, prove_is_move, prove_is_owned},
        quantifiers::{for_all, map},
        red_terms::{red_term, RedTerm},
    },
};

judgment_fn! {
    pub fn sub_perms(
        env: Env,
        live_after: LivePlaces,
        a: Perm,
        b: Perm,
    ) => () {
        debug(a, b, live_after, env)

        (
            (prove_is_move(&env, &perm_a) => ())
            (prove_is_owned(&env, &perm_a) => ())
            (prove_is_owned(&env, &perm_b) => ())
            ------------------------------- ("my-sub-owned")
            (sub_perms(env, _live_after, perm_a, perm_b) => ())
        )

        (
            (prove_is_move(&env, &perm_a) => ())
            (prove_is_owned(&env, &perm_a) => ())
            (prove_is_copy(&env, &perm_b) => ())
            ------------------------------- ("my-sub-copy")
            (sub_perms(env, _live_after, perm_a, perm_b) => ())
        )

        (
            (prove_is_copy(&env, &perm_a) => ())
            (prove_is_owned(&env, &perm_a) => ())
            (prove_is_copy(&env, &perm_b) => ())
            ------------------------------- ("our-sub-copy")
            (sub_perms(env, _live_after, perm_a, perm_b) => ())
        )

        (
            (simplify_perm(&env, &live_after, &perm_a) => perms_s)
            (for_all(perms_s, &|perm_s| sub_perms(&env, &live_after, perm_s, &perm_b)) => ())
            ------------------------------- ("simplify-lhs")
            (sub_perms(env, live_after, perm_a, perm_b) => ())
        )

        (
            (simplify_perm(&env, &live_after, &perm_b) => perms_simpl)
            (for_all(perms_simpl, &|perm_simpl| sub_perms(&env, &live_after, &perm_a, perm_simpl)) => ())
            ------------------------------- ("simplify-rhs")
            (sub_perms(env, live_after, perm_a, perm_b) => ())
        )

        (
            (sub_perm_heads(env, live_after, perm_a, perm_b) => ())
            ------------------------------- ("sub_perms_relative")
            (sub_perms(env, live_after, perm_a, perm_b) => ())
        )
    }
}

judgment_fn! {
    fn sub_perm_heads(
        env: Env,
        live_after: LivePlaces,
        a: LeafPerms,
        b: LeafPerms,
    ) => () {
        debug(a, b, live_after, env)

        (
            (sub_place_perms(env, live_after, places_a, tail_a, places_b, tail_b) => ())
            ------------------------------- ("shared-shared")
            (sub_perm_heads(env, live_after, Cons(Perm::Shared(places_a), tail_a), Cons(Perm::Shared(places_b), tail_b)) => ())
        )

        (
            (sub_place_perms(env, live_after, places_a, tail_a, places_b, tail_b) => ())
            ------------------------------- ("shared-our_leased")
            (sub_perm_heads(env, live_after, Cons(Perm::Shared(places_a), tail_a), Cons((Perm::Our, Perm::Leased(places_b)), tail_b)) => ())
        )

        (
            (sub_place_perms(env, live_after, places_a, tail_a, places_b, tail_b) => ())
            ------------------------------- ("our_leased-our_leased")
            (sub_perm_heads(env, live_after, Cons((Perm::Our, Perm::Leased(places_a)), tail_a), Cons((Perm::Our, Perm::Leased(places_b)), tail_b)) => ())
        )

        (
            (sub_place_perms(env, live_after, places_a, tail_a, places_b, tail_b) => ())
            ------------------------------- ("leased-leased")
            (sub_perm_heads(env, live_after, Cons(Perm::Leased(places_a), tail_a), Cons(Perm::Leased(places_b), tail_b)) => ())
        )

        (
            (sub_place_perms(env, live_after, places_a, tail_a, places_b, tail_b) => ())
            ------------------------------- ("given-given")
            (sub_perm_heads(env, live_after, Cons(Perm::Given(places_a), tail_a), Cons(Perm::Given(places_b), tail_b)) => ())
        )

        (
            (if var_a == var_b)!
            (sub_perm_tails(env, live_after, tail_a, tail_b) => ())
            ------------------------------- ("var-var")
            (sub_perm_heads(env, live_after, Cons(Perm::Var(var_a), tail_a), Cons(Perm::Var(var_b), tail_b)) => ())
        )

        (
            (if var_a == var_b)!
            (sub_perm_tails(env, live_after, tail_a, tail_b) => ())
            ------------------------------- ("our_leased-our_leased")
            (sub_perm_heads(env, live_after, Cons((Perm::Our, Perm::Var(var_a)), tail_a), Cons((Perm::Our, Perm::Var(var_b)), tail_b)) => ())
        )

        (
            (simplify_perm(&env, &live_after, &perm_a) => perms_as)
            (for_all(perms_as, &|perm_as| sub_perm_heads(&env, &live_after, perm_as, &perm_b)) => ())
            ------------------------------- ("simplify-lhs")
            (sub_perm_heads(env, live_after, perm_a, perm_b) => ())
        )

        (
            (simplify_perm(&env, &live_after, &perm_b) => perms_bs)
            (for_all(perms_bs, &|perm_bs| sub_perm_heads(&env, &live_after, &perm_a, perm_bs)) => ())
            ------------------------------- ("simplify-rhs")
            (sub_perm_heads(env, live_after, perm_a, perm_b) => ())
        )
    }
}

judgment_fn! {
    fn sub_perm_tails(
        env: Env,
        live_after: LivePlaces,
        a: LeafPerms,
        b: LeafPerms,
    ) => () {
        debug(a, b, live_after, env)

        (
            ------------------------------- ("tail-my")
            (sub_perm_tails(_env, _live_after, _perm_a, Perm::My) => ())
        )

        (
            (sub_perm_heads(env, live_after, perm_a, perm_b) => ())
            ------------------------------- ("tail-head")
            (sub_perm_tails(env, live_after, perm_a, perm_b) => ())
        )
    }
}

judgment_fn! {
    fn sub_place_perms(
        env: Env,
        live_after: LivePlaces,
        places_a: Set<Place>,
        tail_a: Perm,
        places_b: Set<Place>,
        tail_b: Perm,
    ) => () {
        debug(places_a, tail_a, places_b, tail_b, live_after, env)

        (
            (if all_prefix_of_any(&places_a, &places_b))
            (sub_perm_tails(env, live_after, tail_a, tail_b) => ())
            ------------------------------- ("places-places")
            (sub_place_perms(env, live_after, places_a, tail_a, places_b, tail_b) => ())
        )
    }
}

fn all_prefix_of_any(places_a: &Set<Place>, places_b: &Set<Place>) -> bool {
    places_a.iter().all(|place_a| {
        places_b
            .iter()
            .any(|place_b| place_b.is_prefix_of(&place_a))
    })
}

judgment_fn! {
    fn simplify_perm(
        env: Env,
        live_after: LivePlaces,
        perm: LeafPerms,
    ) => Vec<Perm> {
        debug(perm, env, live_after)

        // An application `L R` where the right hand side R is copy is
        // equivalent to R.

        (
            (prove_is_copy(&env, &*rhs) => ())
            ------------------------------- ("apply-to-copy")
            (simplify_perm(env, _live_after, Perm::Apply(_lhs, rhs)) => vec![&*rhs])
        )

        // XXX note to self --
        //
        // * we need to consider `shared[p]` and friends where the
        //   type of `p` is copy.

        // When given|leased|shared appear before another perm in the chain,
        // and the place(s) they refer to are dead, we can replace them with the
        // perm after them in the chain.

        (
            (if !places.iter().any(|place| live_after.is_live(&place)))
            (let next_perm = Perm::apply(&perm_0, &perm_1))
            ------------------------------- ("dead-given-tail")
            (simplify_perm(_env, live_after, Cons((Perm::Given(places), perm_0), perm_1)) => vec![next_perm])
        )

        (
            (if !places.iter().any(|place| live_after.is_live(&place)))
            (prove_is_lent(&env, &perm_0) => ())
            (let next_perm = Perm::apply(&perm_0, &perm_1))
            ------------------------------- ("dead-leased-tail")
            (simplify_perm(env, live_after, Cons((Perm::Leased(places), perm_0), perm_1)) => vec![next_perm])
        )

        (
            (if !places.iter().any(|place| live_after.is_live(&place)))
            (prove_is_lent(&env, &perm_0) => ())
            (let next_perm = Perm::apply(Perm::Our, Perm::apply(&perm_0, &perm_1)))
            ------------------------------- ("dead-shared-tail")
            (simplify_perm(env, live_after, Cons((Perm::Shared(places), perm_0), perm_1)) => vec![next_perm])
        )

        // When given|leased|shared appear in the last link of the `red_perm`,
        // and the place(s) they refer to are dead,
        // we can replace them with perm(s) derived from the type of those place(s).

        (
            (map(&places, &|&place| {
                dead_place(&env, &live_after, place).map(|red_term| {
                    red_term.red_perm.clone()
                })
            }) => dead_perms)
            ------------------------------- ("dead-given-up")
            (simplify_perm(env, live_after, Perm::Given(places)) => dead_perms)
        )

        (
            (map(&places, &|&place| {
                dead_place(&env, &live_after, place).flat_map(|red_term| {
                    prove_is_lent(&env, &red_term).map(|()| {
                        red_term.red_perm.clone()
                    })
                })
            }) => dead_perms)
            ------------------------------- ("dead_leased-up")
            (simplify_perm(env, live_after, Perm::Leased(places)) => dead_perms)
        )

        (
            (map(&places, &|&place| {
                dead_place(&env, &live_after, place).flat_map(|red_term| {
                    prove_is_lent(&env, &red_term).map(|()| {
                        Perm::apply(Perm::Our, &red_term.red_perm)
                    })
                })
            }) => dead_perms)
            ------------------------------- ("dead_shared-up")
            (simplify_perm(env, live_after, Perm::Shared(places)) => dead_perms)
        )
    }
}

judgment_fn! {
    fn dead_place(
        env: Env,
        live_after: LivePlaces,
        place: Place,
    ) => RedTerm {
        debug(env, live_after, place)

        (
            (if !live_after.is_live(&place))!
            (let ty = env.place_ty(&place)?)
            (red_term(&env, &ty) => red_term)
            ------------------------------- ("dead_place")
            (dead_place(env, live_after, place) => red_term)
        )
    }
}

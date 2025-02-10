use formality_core::{judgment_fn, Cons, Set};

use crate::{
    grammar::{NamedTy, Parameter, VarianceKind},
    type_system::{
        env::Env,
        liveness::LivePlaces,
        quantifiers::for_all,
        red_terms::{red_term_under, Chain, Lien, RedTy, TyChain},
    },
};

judgment_fn! {
    /// Provable if `a <: b` in an owned (`my`) context.
    pub fn sub(
        env: Env,
        live_after: LivePlaces,
        a: Parameter,
        b: Parameter,
    ) => () {
        debug(a, b, live_after, env)

        (
            (sub_under_perms(env, live_after, Chain::my(), a, Chain::my(), b) => ())
            ------------------------------- ("sub")
            (sub(env, live_after, a, b) => ())
        )
    }
}

judgment_fn! {
    /// Provable if `a <: b` in an owned (`my`) context.
    fn sub_under_perms(
        env: Env,
        live_after: LivePlaces,
        chain_a: Chain,
        a: Parameter,
        chain_b: Chain,
        b: Parameter,
    ) => () {
        debug(chain_a, a, chain_b, b, live_after, env)

        (
            (red_term_under(&env, &chain_a, &a) => red_term_a)
            (red_term_under(&env, &chain_b, &b) => red_term_b)
            (let ty_chains_a = red_term_a.ty_chains())
            (let ty_chains_b = red_term_b.ty_chains())
            (for_all(&ty_chains_a, &|ty_chain_a| sub_some(&env, &live_after, ty_chain_a, &ty_chains_b)) => ())
            ------------------------------- ("sub")
            (sub_under_perms(env, live_after, chain_a, a, chain_b, b) => ())
        )
    }
}

judgment_fn! {
    fn sub_some(
        env: Env,
        live_after: LivePlaces,
        ty_chain_a: TyChain,
        ty_chains_b: Set<TyChain>,
    ) => () {
        debug(ty_chain_a, ty_chains_b, live_after, env)

        (
            (&ty_chains_b => ty_chain_b)
            (sub_ty_chain(&env, &live_after, &ty_chain_a, &ty_chain_b) => ())
            ------------------------------- ("sub-some")
            (sub_some(env, live_after, ty_chain_a, ty_chains_b) => ())
        )
    }
}

judgment_fn! {
    fn sub_ty_chain(
        env: Env,
        live_after: LivePlaces,
        ty_chain_a: TyChain,
        ty_chain_b: TyChain,
    ) => () {
        debug(ty_chain_a, ty_chain_b, live_after, env)

        (
            (if let TyChain { chain: chain_a, ty: RedTy::Var(var_a) } = ty_chain_a)
            (if let TyChain { chain: chain_b, ty: RedTy::Var(var_b) } = ty_chain_b)
            (if var_a == var_b)!
            (sub_chains(env, live_after, chain_a, chain_b) => ())
            ------------------------------- ("sub-vars-eq")
            (sub_ty_chain(env, live_after, ty_chain_a, ty_chain_b) => ())
        )

        (
            (if let TyChain { chain: chain_a, ty: RedTy::NamedTy(NamedTy { name: name_a, parameters: parameters_a }) } = ty_chain_a)
            (if let TyChain { chain: chain_b, ty: RedTy::NamedTy(NamedTy { name: name_b, parameters: parameters_b }) } = ty_chain_b)
            (if name_a == name_b)!
            (sub_chains(&env, &live_after, &chain_a, &chain_b) => ())
            (let variances = env.variances(&name_a)?)
            (if parameters_a.len() == variances.len())
            (if parameters_b.len() == variances.len())
            (for_all(0..variances.len(), &|&i| {
                sub_generic_parameter(&env, &live_after, &variances[i], &chain_a, &parameters_a[i], &chain_b, &parameters_b[i])
            }) => ())
            ------------------------------- ("sub-named")
            (sub_ty_chain(env, live_after, ty_chain_a, ty_chain_b) => ())
        )

        (
            (if let TyChain { chain: chain_a, ty: RedTy::None } = ty_chain_a)
            (if let TyChain { chain: chain_b, ty: RedTy::None } = ty_chain_b)!
            (sub_chains(env, live_after, chain_a, chain_b) => ())
            ------------------------------- ("sub-no-data")
            (sub_ty_chain(env, live_after, ty_chain_a, ty_chain_b) => ())
        )
    }
}

judgment_fn! {
    fn sub_chains(
        env: Env,
        live_after: LivePlaces,
        chain_a: Chain,
        chain_b: Chain,
    ) => () {
        debug(chain_a, chain_b, live_after, env)

        (
            (if chain_a.is_owned(&env))
            (if chain_a.is_moved(&env))
            (if chain_b.is_owned(&env))
            ------------------------------- ("my-sub-owned")
            (sub_chains(env, _live_after, chain_a, chain_b) => ())
        )

        (
            (if chain_a.is_owned(&env))
            (if chain_a.is_moved(&env))
            (if chain_b.is_copy(&env))
            ------------------------------- ("my-sub-copy")
            (sub_chains(env, _live_after, chain_a, chain_b) => ())
        )

        (
            (if chain_a.is_owned(&env))
            (if chain_a.is_copy(&env))
            (if chain_b.is_copy(&env))
            ------------------------------- ("our-sub-copy")
            (sub_chains(env, _live_after, chain_a, chain_b) => ())
        )

        (
            (let chain_a: Chain = chain_a)
            (let chain_b: Chain = chain_b)
            (if place_b.is_prefix_of(&place_a))
            (sub_chains(env, live_after, chain_a, chain_b) => ())
            ------------------------------- ("shared-vs-shared")
            (sub_chains(env, live_after, Cons(Lien::Shared(place_a), chain_a), Cons(Lien::Shared(place_b), chain_b)) => ())
        )

        (
            (let chain_a: Chain = chain_a)
            (let chain_b: Chain = chain_b)
            (if place_b.is_prefix_of(&place_a))
            (sub_chains(env, live_after, chain_a, chain_b) => ())
            ------------------------------- ("shared-vs-our-leased")
            (sub_chains(env, live_after, Cons(Lien::Shared(place_a), chain_a), Cons(Lien::Our, Cons(Lien::Leased(place_b), chain_b))) => ())
        )

        (
            (let chain_a: Chain = chain_a)
            (let chain_b: Chain = chain_b)
            (if place_b.is_prefix_of(&place_a))
            (sub_chains(env, live_after, chain_a, chain_b) => ())
            ------------------------------- ("leased-vs-leased")
            (sub_chains(env, live_after, Cons(Lien::Leased(place_a), chain_a), Cons(Lien::Leased(place_b), chain_b)) => ())
        )

        (
            (let chain_a: Chain = chain_a)
            (let chain_b: Chain = chain_b)
            (sub_chains(env, live_after, chain_a, chain_b) => ())
            ------------------------------- ("our-vs-our")
            (sub_chains(env, live_after, Cons(Lien::Our, chain_a), Cons(Lien::Our, chain_b)) => ())
        )

        (
            (let chain_a: Chain = chain_a)
            (let chain_b: Chain = chain_b)
            (if var_a == var_b)!
            (sub_chains(env, live_after, chain_a, chain_b) => ())
            ------------------------------- ("var-vs-var")
            (sub_chains(env, live_after, Cons(Lien::Variable(var_a), chain_a), Cons(Lien::Variable(var_b), chain_b)) => ())
        )

        (
            (let chain_a: Chain = chain_a)
            (if chain_a.is_lent(&env))
            (if !live_after.is_live(&place_a))
            (sub_chains(env, live_after, chain_a, chain_b) => ())
            ------------------------------- ("leased-dead")
            (sub_chains(env, live_after, Cons(Lien::Leased(place_a), chain_a), chain_b) => ())
        )

        (
            (let chain_a: Chain = chain_a)
            (if chain_a.is_lent(&env))
            (if !live_after.is_live(&place_a))
            (sub_chains(&env, live_after, Chain::our().concat(&env, chain_a), chain_b) => ())
            ------------------------------- ("shared-dead")
            (sub_chains(env, live_after, Cons(Lien::Shared(place_a), chain_a), chain_b) => ())
        )
    }
}

judgment_fn! {
    fn sub_generic_parameter(
        env: Env,
        live_after: LivePlaces,
        variances: Vec<VarianceKind>,
        liens_a: Chain,
        a: Parameter,
        liens_b: Chain,
        b: Parameter,
    ) => () {
        debug(variances, a, b, liens_a, liens_b, live_after, env)

        // invariant is always ok

        (
            (sub(&env, &live_after, &a, &b) => ())
            (sub(&env, &live_after, &b, &a) => ())
            ------------------------------- ("invariant")
            (sub_generic_parameter(env, live_after, _v, _perms_a, a, _perms_b, b) => ())
        )

        // We want to allow covariant unless the values are leased.
        // We do that by allowing it if the target type is `copy` or `my`.
        //
        // Here we rule out any form of variance (relative, atomic) and
        // limit that to invariant. This is stricter than needed.

        (
            (if perms_b.is_copy(&env))
            (sub_under_perms(&env, &live_after, &perms_a, &a, &perms_b, &b) => ())
            ------------------------------- ("covariant-copy")
            (sub_generic_parameter(env, live_after, (), perms_a, a, perms_b, b) => ())
        )

        (
            (if perms_b.is_owned(&env))
            (sub_under_perms(&env, &live_after, &perms_a, &a, &perms_b, &b) => ())
            ------------------------------- ("covariant-owned")
            (sub_generic_parameter(env, live_after, (), perms_a, a, perms_b, b) => ())
        )
    }
}

trait Implies {
    fn implies(self, other: bool) -> bool;
}

impl Implies for bool {
    fn implies(self, other: bool) -> bool {
        !self || (self && other)
    }
}

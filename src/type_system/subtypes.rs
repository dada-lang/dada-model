use formality_core::{judgment_fn, Cons, Set};

use crate::{
    grammar::{NamedTy, Parameter, Perm, Place, Ty, VarianceKind},
    type_system::{
        env::Env,
        is_::{lien_chain_is_leased, lien_chain_is_shared},
        lien_chains::{lien_chains, ty_chains, Lien, LienChain, My, Our, TyChain},
        lien_set::lien_set_from_chain,
        liveness::LivePlaces,
        quantifiers::{fold, fold_zipped},
    },
};

judgment_fn! {
    /// Provable if `a <: b` in an owned (`my`) context.
    pub fn sub(
        env: Env,
        live_after: LivePlaces,
        a: Parameter,
        b: Parameter,
    ) => Env {
        debug(a, b, live_after, env)

        (
            (sub_in_cx(env, live_after, My(), a, My(), b) => env)
            ------------------------------- ("sub")
            (sub(env, live_after, a, b) => env)
        )
    }
}

judgment_fn! {
    /// Provable if `a <: b` when appearing in the context of lien chains `chain_a` and `chain_b` respectively.
    fn sub_in_cx(
        env: Env,
        live_after: LivePlaces,
        cx_a: LienChain,
        a: Parameter,
        cx_b: LienChain,
        b: Parameter,
    ) => Env {
        debug(cx_a, a, cx_b, b, live_after, env)

        (
            (ty_chains(&env, cx_a, a) => ty_liens_a)
            (ty_chains(&env, &cx_b, &b) => ty_liens_b)
            (sub_ty_chain_sets(&env, &live_after, &ty_liens_a, ty_liens_b) => env)
            ------------------------------- ("sub")
            (sub_in_cx(env, live_after, cx_a, a: Ty, cx_b, b: Ty) => env)
        )

        (
            (lien_chains(&env, cx_a, a) => chain_a)
            (lien_chains(&env, &cx_b, &b) => chain_b)
            (sub_lien_chain_sets(&env, &live_after, &chain_a, chain_b) => env)
            ------------------------------- ("sub")
            (sub_in_cx(env, live_after, cx_a, a: Perm, cx_b, b: Perm) => env)
        )
    }
}

judgment_fn! {
    fn sub_ty_chain_sets(
        env: Env,
        live_after: LivePlaces,
        ty_liens_a: Set<TyChain>,
        ty_liens_b: Set<TyChain>,
    ) => Env {
        debug(ty_liens_a, ty_liens_b, live_after, env)

        (
            ------------------------------- ("nil")
            (sub_ty_chain_sets(env, _live_after, (), _b_s) => env)
        )

        (
            (&b_s => b)
            (sub_ty_chains(&env, &live_after, &a, &b) => env)
            (sub_ty_chain_sets(env, &live_after, &a_s, &b_s) => env)
            ------------------------------- ("cons")
            (sub_ty_chain_sets(env, live_after, Cons(a, a_s), b_s) => env)
        )
    }
}

judgment_fn! {
    fn sub_ty_chains(
        env: Env,
        live_after: LivePlaces,
        ty_chain_a: TyChain,
        ty_chain_b: TyChain,
    ) => Env {
        debug(ty_chain_a, ty_chain_b, live_after, env)

        (
            (if a == b)!
            (sub_lien_chains(env, live_after, &chain_a, &chain_b) => env)
            (compatible_layout(env, &chain_a, &chain_b) => env)
            -------------------------------- ("var")
            (sub_ty_chains(env, live_after, TyChain::Var(chain_a, a), TyChain::Var(chain_b, b)) => env)
        )

        (
            (let NamedTy { name: name_a, parameters: parameters_a } = a)
            (let NamedTy { name: name_b, parameters: parameters_b } = b)
            (if name_a == name_b) // FIXME: subtyping between classes
            (if env.is_class_ty(&name_a))!
            (sub_lien_chains(env, &live_after, &chain_a, &chain_b) => env)
            (let variances = env.variances(&name_a)?)
            (if parameters_a.len() == variances.len())
            (if parameters_b.len() == variances.len())
            (fold(env, 0..variances.len(), &|env, &i| {
                sub_generic_parameter(env, &live_after, &variances[i], &chain_a, &parameters_a[i], &chain_b, &parameters_b[i])
            }) => env)
            (compatible_layout(env, &chain_a, &chain_b) => env)
            -------------------------------- ("class ty")
            (sub_ty_chains(env, live_after, TyChain::NamedTy(chain_a, a), TyChain::NamedTy(chain_b, b)) => env)
        )

        (
            (let NamedTy { name: name_a, parameters: parameters_a } = a)
            (let NamedTy { name: name_b, parameters: parameters_b } = b)
            (if name_a == name_b)
            (if env.is_value_ty(&name_a))!
            (fold_zipped(env, &parameters_a, &parameters_b, &|env, parameter_a, parameter_b| {
                sub_in_cx(env, &live_after, &chain_a, parameter_a, &chain_b, parameter_b)
            }) => env)
            -------------------------------- ("value ty")
            (sub_ty_chains(env, live_after, TyChain::NamedTy(chain_a, a), TyChain::NamedTy(chain_b, b)) => env)
        )
    }
}

judgment_fn! {
    fn compatible_layout(
        env: Env,
        chain_a: LienChain,
        chain_b: LienChain,
    ) => Env {
        debug(chain_a, chain_b, env)

        trivial(chain_a == chain_b => env)

        (
            (lien_chain_is_shared(&env, chain) => ())
            ------------------------------- ("my-shared")
            (compatible_layout(env, My(), chain) => &env)
        )

        (
            (lien_chain_is_shared(&env, chain) => ())
            ------------------------------- ("shared-my")
            (compatible_layout(env, chain, My()) => &env)
        )

        (
            (if chain_a.is_not_my() && chain_b.is_not_my())!
            (lien_chain_is_shared(&env, chain_a) => ())
            (lien_chain_is_shared(&env, &chain_b) => ())
            ------------------------------- ("shared-shared")
            (compatible_layout(env, chain_a, chain_b) => &env)
        )

        (
            (if chain_a.is_not_my() && chain_b.is_not_my())!
            (lien_chain_is_leased(&env, chain_a) => ())
            (lien_chain_is_leased(&env, &chain_b) => ())
            ------------------------------- ("leased-leased")
            (compatible_layout(env, chain_a, chain_b) => &env)
        )
    }
}

judgment_fn! {
    fn sub_generic_parameter(
        env: Env,
        live_after: LivePlaces,
        variances: Vec<VarianceKind>,
        cx_a: LienChain,
        a: Parameter,
        cx_b: LienChain,
        b: Parameter,
    ) => Env {
        debug(variances, cx_a, a, cx_b, b, live_after, env)

        // FIXME: this may be stricter than needed: we may everything invariant
        // even if it's just relative and not atomic, is that correct?

        (
            (sub_in_cx(env, &live_after, My(), &a, My(), &b) => env)
            (sub_in_cx(env, &live_after, My(), &b, My(), &a) => env)
            ------------------------------- ("invariant")
            (sub_generic_parameter(env, live_after, _variances, _cx_a, a, _cx_b, b) => env)
        )

        (
            (lien_chain_is_shared(&env, &cx_a) => ())
            (sub_in_cx(&env, &live_after, &cx_a, &a, &cx_b, &b) => env)
            ------------------------------- ("shared_a")
            (sub_generic_parameter(env, live_after, (), cx_a, a, cx_b, b) => env)
        )

        (
            (lien_chain_is_shared(&env, &cx_b) => ())
            (sub_in_cx(&env, &live_after, &cx_a, &a, &cx_b, &b) => env)
            ------------------------------- ("shared_b")
            (sub_generic_parameter(env, live_after, (), cx_a, a, cx_b, b) => env)
        )

        (
            (sub_in_cx(env, live_after, My(), a, My(), b) => env)
            ------------------------------- ("my")
            (sub_generic_parameter(env, live_after, (), My(), a, My(), b) => env)
        )
    }
}

judgment_fn! {
    /// Provable if every chain in `chains_a` is a subchain of some chain in `chains_b`.
    fn sub_lien_chain_sets(
        env: Env,
        live_after: LivePlaces,
        chains_a: Set<LienChain>,
        chains_b: Set<LienChain>,
    ) => Env {
        debug(chains_a, chains_b, live_after, env)

        (
            ------------------------------- ("nil")
            (sub_lien_chain_sets(env, _live_after, (), _chains_b) => env)
        )

        (
            (&chains_b => chain_b)
            (sub_lien_chains(&env, &live_after, &chain_a, &chain_b) => env)
            (sub_lien_chain_sets(env, &live_after, &chains_a, &chains_b) => env)
            ------------------------------- ("cons")
            (sub_lien_chain_sets(env, live_after, Cons(chain_a, chains_a), chains_b) => env)
        )
    }
}

judgment_fn! {
    fn sub_lien_chains(
        env: Env,
        live_after: LivePlaces,
        a: LienChain,
        b: LienChain,
    ) => Env {
        debug(a, b, live_after, env)

        // Special cases for fully owned things

        (
            --------------------------- ("my-*")
            (sub_lien_chains(env, _live_after, My(), _b) => env)
        )

        (
            --------------------------- ("our-sh")
            (sub_lien_chains(env, _live_after, Our(), Cons(Lien::Shared(_), _)) => env)
        )

        (
            (lien_covered_by(lien_a, lien_b) => ())
            (sub_lien_chain_exts(&env, &chain_a, &chain_b) => env)
            --------------------------- ("matched starts")
            (sub_lien_chains(env, _live_after, Cons(lien_a, chain_a), Cons(lien_b, chain_b)) => &env)
        )

        (
            (lien_chain_is_leased(&env, &chain_a) => ())
            (if !live_after.is_live(place))
            (sub_lien_chains(&env, &live_after, Cons(Lien::Our, &chain_a), &chain_b) => env)
            --------------------------- ("cancel shared")
            (sub_lien_chains(env, live_after, Cons(Lien::Shared(place), chain_a), chain_b) => env)
        )

        (
            (lien_chain_is_leased(&env, &chain_a) => ())
            (if !live_after.is_live(place))
            (sub_lien_chains(&env, &live_after, &chain_a, &chain_b) => env)
            --------------------------- ("cancel leased")
            (sub_lien_chains(env, live_after, Cons(Lien::Leased(place), chain_a), chain_b) => env)
        )
    }
}
judgment_fn! {
    fn sub_lien_chain_exts(
        env: Env,
        a: LienChain,
        b: LienChain,
    ) => Env {
        debug(a, b, env)

        (
            (lien_set_from_chain(&env, &chain_a) => lien_set_a)
            (lien_set_from_chain(&env, &chain_b) => lien_set_b)
            (lien_set_covered_by(&lien_set_a, lien_set_b) => ())
            (lien_chain_covered_by(&chain_a, &chain_b) => ())
            --------------------------- ("chain-chain")
            (sub_lien_chain_exts(env, chain_a, chain_b) => &env)
        )
    }
}

judgment_fn! {
    fn lien_set_covered_by(
        a: Set<Lien>,
        b: Set<Lien>,
    ) => () {
        debug(a, b)

        (
            ------------------------------- ("nil")
            (lien_set_covered_by((), _b) => ())
        )

        (
            (&b_s => b)
            (lien_covered_by(&a, b) => ())
            (lien_set_covered_by(&a_s, &b_s) => ())
            ------------------------------- ("cons")
            (lien_set_covered_by(Cons(a, a_s), b_s) => ())
        )
    }
}

judgment_fn! {
    fn lien_chain_covered_by(
        a: LienChain,
        b: LienChain,
    ) => () {
        debug(a, b)

        (
            (lien_chain_covered_by(chain_a, chain_b) => ())
            ------------------------------- ("skip lease prefix")
            (lien_chain_covered_by(Cons(Lien::Leased(_), chain_a), chain_b) => ())
        )

        (
            (lien_chain_strictly_covered_by(chain_a, chain_b) => ())
            ------------------------------- ("strictly covered")
            (lien_chain_covered_by(chain_a, chain_b) => ())
        )
    }
}

judgment_fn! {
    fn lien_chain_strictly_covered_by(
        a: LienChain,
        b: LienChain,
    ) => () {
        debug(a, b)

        (
            ------------------------------- ("my-my")
            (lien_chain_strictly_covered_by(My(), My()) => ())
        )

        (
            (lien_covered_by(lien_a, lien_b) => ())
            (lien_chain_strictly_covered_by(&chain_a, &chain_b) => ())
            ------------------------------- ("lien-lien")
            (lien_chain_strictly_covered_by(Cons(lien_a, chain_a), Cons(lien_b, chain_b)) => ())
        )
    }
}

judgment_fn! {
    fn lien_covered_by(
        a: Lien,
        b: Lien,
    ) => () {
        debug(a, b)

        (
            ------------------------------- ("our-our")
            (lien_covered_by(Lien::Our, Lien::Our) => ())
        )

        (
            (if place_covered_by_place(&a, &b))
            ------------------------------- ("lease-lease")
            (lien_covered_by(Lien::Leased(a), Lien::Leased(b)) => ())
        )

        (
            (if place_covered_by_place(&a, &b))
            ------------------------------- ("shared-shared")
            (lien_covered_by(Lien::Shared(a), Lien::Shared(b)) => ())
        )

        (
            (if a == b)
            ------------------------------- ("var-var")
            (lien_covered_by(Lien::Var(a), Lien::Var(b)) => ())
        )
    }
}

/// A place P1 *covers* a place P2 if it is a prefix:
/// for example, `x.y` covers `x.y` and `x.y.z` but not `x.z` or `x1`.
#[tracing::instrument(level = "Debug", ret)]
fn place_covered_by_place(place: &Place, covering_place: &Place) -> bool {
    covering_place.is_prefix_of(place)
}

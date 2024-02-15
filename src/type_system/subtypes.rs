use formality_core::{judgment_fn, Cons, Set};

use crate::{
    grammar::{NamedTy, Parameter, Perm, Place, Ty},
    type_system::{
        env::Env,
        flow::Flow,
        liens::{lien_chains, ty_chains, Lien, LienChain, My, Our, TyChain},
        quantifiers::fold_zipped,
    },
};

judgment_fn! {
    /// Provable if `a <: b` in an owned (`my`) context.
    pub fn sub(
        env: Env,
        flow: Flow,
        a: Parameter,
        b: Parameter,
    ) => (Env, Flow) {
        debug(a, b, env, flow)

        (
            (sub_in_cx(env, flow, My(), a, My(), b) => (env, flow))
            ------------------------------- ("sub")
            (sub(env, flow, a, b) => (env, flow))
        )
    }
}

judgment_fn! {
    /// Provable if `a <: b` when appearing in the context of lien chains `chain_a` and `chain_b` respectively.
    fn sub_in_cx(
        env: Env,
        flow: Flow,
        chain_a: LienChain,
        a: Parameter,
        chain_b: LienChain,
        b: Parameter,
    ) => (Env, Flow) {
        debug(chain_a, a, chain_b, b, env, flow)

        (
            (ty_chains(env, liens_a, a) => (env, ty_liens_a))
            (ty_chains(env, &liens_b, &b) => (env, ty_liens_b))
            (sub_ty_chain_sets(env, &flow, &ty_liens_a, ty_liens_b) => (env, flow))
            ------------------------------- ("sub")
            (sub_in_cx(env, flow, liens_a, a: Ty, liens_b, b: Ty) => (env, flow))
        )

        (
            (lien_chains(env, liens_a, a) => (env, liens_a))
            (lien_chains(env, &liens_b, &b) => (env, liens_b))
            (sub_lien_chain_sets(env, &flow, &liens_a, liens_b) => (env, flow))
            ------------------------------- ("sub")
            (sub_in_cx(env, flow, liens_a, a: Perm, liens_b, b: Perm) => (env, flow))
        )
    }
}

judgment_fn! {
    fn sub_ty_chain_sets(
        env: Env,
        flow: Flow,
        ty_liens_a: Set<TyChain>,
        ty_liens_b: Set<TyChain>,
    ) => (Env, Flow) {
        debug(ty_liens_a, ty_liens_b, env, flow)

        (
            ------------------------------- ("nil")
            (sub_ty_chain_sets(env, flow, (), _b_s) => (env, flow))
        )

        (
            (&b_s => b)
            (sub_ty_chains(&env, &flow, &a, &b) => (env, flow))
            (sub_ty_chain_sets(env, flow, &a_s, &b_s) => (env, flow))
            ------------------------------- ("cons")
            (sub_ty_chain_sets(env, flow, Cons(a, a_s), b_s) => (env, flow))
        )
    }
}

judgment_fn! {
    fn sub_ty_chains(
        env: Env,
        flow: Flow,
        ty_chain_a: TyChain,
        ty_chain_b: TyChain,
    ) => (Env, Flow) {
        debug(ty_chain_a, ty_chain_b, env, flow)

        (
            (if a == b)!
            (sub_lien_chains(env, flow, chain_a, chain_b) => (env, flow))
            (let layout_a = ty_chain_a.lien_chain().layout())
            (let layout_b = ty_chain_b.lien_chain().layout())
            (if layout_a == layout_b)
            -------------------------------- ("var")
            (sub_ty_chains(env, flow, TyChain::Var(chain_a, a), TyChain::Var(chain_b, b)) => (env, flow))
        )

        (
            (let NamedTy { name: name_a, parameters: parameters_a } = a)
            (let NamedTy { name: name_b, parameters: parameters_b } = b)
            (if name_a == name_b)! // FIXME: subtyping between classes
            (sub_lien_chains(env, flow, &chain_a, &chain_b) => (env, flow))
            (fold_zipped((env, flow), &parameters_a, &parameters_b, &|(env, flow), parameter_a, parameter_b| {
                sub_in_cx(env, flow, &chain_a, parameter_a, &chain_b, parameter_b)
            }) => (env, flow))
            (let layout_a = ty_chain_a.lien_chain().layout())
            (let layout_b = ty_chain_b.lien_chain().layout())
            (if layout_a == layout_b) // FIXME: should consider if these are boxed classes
            -------------------------------- ("named ty")
            (sub_ty_chains(env, flow, TyChain::NamedTy(chain_a, a), TyChain::NamedTy(chain_b, b)) => (env, flow))
        )
    }
}

judgment_fn! {
    /// Provable if every chain in `chains_a` is a subchain of some chain in `chains_b`.
    fn sub_lien_chain_sets(
        env: Env,
        flow: Flow,
        chains_a: Set<LienChain>,
        chains_b: Set<LienChain>,
    ) => (Env, Flow) {
        debug(chains_a, chains_b, env, flow)

        (
            ------------------------------- ("nil")
            (sub_lien_chain_sets(env, flow, (), _chains_b) => (env, flow))
        )

        (
            (&chains_b => chain_b)
            (sub_lien_chains(&env, &flow, &chain_a, &chain_b) => (env, flow))
            (sub_lien_chain_sets(env, flow, &chains_a, &chains_b) => (env, flow))
            ------------------------------- ("cons")
            (sub_lien_chain_sets(env, flow, Cons(chain_a, chains_a), chains_b) => (env, flow))
        )
    }
}

judgment_fn! {
    pub fn sub_lien_chains(
        env: Env,
        flow: Flow,
        a: LienChain,
        b: LienChain,
    ) => (Env, Flow) {
        debug(a, b, env, flow)

        (
            --------------------------- ("my-*")
            (sub_lien_chains(env, flow, My(), _b) => (env, flow))
        )

        (
            --------------------------- ("our-our")
            (sub_lien_chains(env, flow, Our(), Our()) => (env, flow))
        )

        (
            --------------------------- ("our-sh")
            (sub_lien_chains(env, flow, Our(), Cons(Lien::Shared(_), _)) => (env, flow))
        )

        (
            (if place_covered_by_place(&a, &b))
            (lien_chain_covered_by(chain_a, chain_b) => ())
            --------------------------- ("sh-sh")
            (sub_lien_chains(env, flow, Cons(Lien::Shared(a), chain_a), Cons(Lien::Shared(b), chain_b)) => (&env, &flow))
        )

        (
            (if place_covered_by_place(&a, &b))
            (lien_chain_strictly_covered_by(chain_a, chain_b) => ())
            --------------------------- ("l-l")
            (sub_lien_chains(env, flow, Cons(Lien::Leased(a), chain_a), Cons(Lien::Leased(b), chain_b)) => (&env, &flow))
        )

        (
            (if a == b)!
            (lien_chain_covered_by(chain_a, chain_b) => ())
            --------------------------- ("l-l")
            (sub_lien_chains(env, flow, Cons(Lien::Var(a), chain_a), Cons(Lien::Var(b), chain_b)) => (&env, &flow))
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
            (if place_covered_by_place(&a, &b))
            (lien_chain_strictly_covered_by(chain_a, chain_b) => ())
            ------------------------------- ("lease-lease")
            (lien_chain_strictly_covered_by(Cons(Lien::Leased(a), chain_a), Cons(Lien::Leased(b), chain_b)) => ())
        )

        (
            (if a == b)
            (lien_chain_strictly_covered_by(chain_a, chain_b) => ())
            ------------------------------- ("var-var")
            (lien_chain_strictly_covered_by(Cons(Lien::Var(a), chain_a), Cons(Lien::Var(b), chain_b)) => ())
        )
    }
}

/// A place P1 *covers* a place P2 if it is a prefix:
/// for example, `x.y` covers `x.y` and `x.y.z` but not `x.z` or `x1`.
#[tracing::instrument(level = "Debug", ret)]
fn place_covered_by_place(place: &Place, covering_place: &Place) -> bool {
    covering_place.is_prefix_of(place)
}

#[cfg(test)]
mod tests;

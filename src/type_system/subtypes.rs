use formality_core::{judgment_fn, Cons, Set};

use crate::{
    grammar::{NamedTy, Parameter, Perm, Place, Ty},
    type_system::{
        env::Env,
        flow::Flow,
        liens::{liens, ty_liens, Lien, Liens, My, Our, TyLiens},
        quantifiers::fold_zipped,
    },
};

judgment_fn! {
    pub fn sub(
        env: Env,
        flow: Flow,
        a: Parameter,
        b: Parameter,
    ) => (Env, Flow) {
        debug(a, b, env, flow)

        (
            (sub_cx(env, flow, My(), a, My(), b) => (env, flow))
            ------------------------------- ("sub")
            (sub(env, flow, a, b) => (env, flow))
        )
    }
}

judgment_fn! {
    fn sub_cx(
        env: Env,
        flow: Flow,
        liens_a: Liens,
        a: Parameter,
        liens_b: Liens,
        b: Parameter,
    ) => (Env, Flow) {
        debug(liens_a, a, liens_b, b, env, flow)

        (
            (ty_liens(env, liens_a, a) => (env, ty_liens_a))
            (ty_liens(env, &liens_b, &b) => (env, ty_liens_b))
            (sub_ty_liens_sets(env, &flow, &ty_liens_a, ty_liens_b) => (env, flow))
            ------------------------------- ("sub")
            (sub_cx(env, flow, liens_a, a: Ty, liens_b, b: Ty) => (env, flow))
        )

        (
            (liens(env, liens_a, a) => (env, liens_a))
            (liens(env, &liens_b, &b) => (env, liens_b))
            (sub_liens_sets(env, &flow, &liens_a, liens_b) => (env, flow))
            ------------------------------- ("sub")
            (sub_cx(env, flow, liens_a, a: Perm, liens_b, b: Perm) => (env, flow))
        )
    }
}

judgment_fn! {
    fn sub_ty_liens_sets(
        env: Env,
        flow: Flow,
        ty_liens_a: Set<TyLiens>,
        ty_liens_b: Set<TyLiens>,
    ) => (Env, Flow) {
        debug(ty_liens_a, ty_liens_b, env, flow)

        (
            ------------------------------- ("nil")
            (sub_ty_liens_sets(env, flow, (), _b_s) => (env, flow))
        )

        (
            (&b_s => b)
            (sub_ty_liens(&env, &flow, &a, &b) => (env, flow))
            (sub_ty_liens_sets(env, flow, &a_s, &b_s) => (env, flow))
            ------------------------------- ("cons")
            (sub_ty_liens_sets(env, flow, Cons(a, a_s), b_s) => (env, flow))
        )
    }
}

judgment_fn! {
    fn sub_ty_liens(
        env: Env,
        flow: Flow,
        ty_liens_a: TyLiens,
        ty_liens_b: TyLiens,
    ) => (Env, Flow) {
        debug(ty_liens_a, ty_liens_b, env, flow)

        (
            (if a == b)!
            // (let layout_a = liens_a.layout())
            // (let layout_b = liens_b.layout())
            // (if layout_a == layout_b)
            (sub_liens(env, flow, liens_a, liens_b) => (env, flow))
            -------------------------------- ("var")
            (sub_ty_liens(env, flow, TyLiens::Var(liens_a, a), TyLiens::Var(liens_b, b)) => (env, flow))
        )

        (
            (let NamedTy { name: name_a, parameters: parameters_a } = a)
            (let NamedTy { name: name_b, parameters: parameters_b } = b)
            (if name_a == name_b)! // FIXME: subtyping between classes
            // (let layout_a = liens_a.layout())
            // (let layout_b = liens_b.layout())
            // (if layout_a == layout_b) // FIXME: should consider if these are boxed classes
            (sub_liens(env, flow, &liens_a, &liens_b) => (env, flow))
            (fold_zipped((env, flow), &parameters_a, &parameters_b, &|(env, flow), parameter_a, parameter_b| {
                sub_cx(env, flow, &liens_a, parameter_a, &liens_b, parameter_b)
            }) => (env, flow))
            -------------------------------- ("named ty")
            (sub_ty_liens(env, flow, TyLiens::NamedTy(liens_a, a), TyLiens::NamedTy(liens_b, b)) => (env, flow))
        )
    }
}

judgment_fn! {
    fn sub_liens_sets(
        env: Env,
        flow: Flow,
        liens_a: Set<Liens>,
        liens_b: Set<Liens>,
    ) => (Env, Flow) {
        debug(liens_a, liens_b, env, flow)

        (
            ------------------------------- ("nil")
            (sub_liens_sets(env, flow, (), _b_s) => (env, flow))
        )

        (
            (&b_s => b)
            (sub_liens(&env, &flow, &a, &b) => (env, flow))
            (sub_liens_sets(env, flow, &a_s, &b_s) => (env, flow))
            ------------------------------- ("cons")
            (sub_liens_sets(env, flow, Cons(a, a_s), b_s) => (env, flow))
        )
    }
}

judgment_fn! {
    pub fn sub_liens(
        env: Env,
        flow: Flow,
        a: Liens,
        b: Liens,
    ) => (Env, Flow) {
        debug(a, b, env, flow)

        (
            --------------------------- ("my-*")
            (sub_liens(env, flow, My(), _b) => (env, flow))
        )

        (
            --------------------------- ("our-our")
            (sub_liens(env, flow, Our(), Our()) => (env, flow))
        )

        (
            --------------------------- ("our-sh")
            (sub_liens(env, flow, Our(), Cons(Lien::Shared(_), _)) => (env, flow))
        )

        (
            (if place_covered_by_place(&a, &b))
            (liens_covered_by(liens_a, liens_b) => ())
            --------------------------- ("sh-sh")
            (sub_liens(env, flow, Cons(Lien::Shared(a), liens_a), Cons(Lien::Shared(b), liens_b)) => (&env, &flow))
        )

        (
            (if place_covered_by_place(&a, &b))
            (liens_strictly_covered_by(liens_a, liens_b) => ())
            --------------------------- ("l-l")
            (sub_liens(env, flow, Cons(Lien::Leased(a), liens_a), Cons(Lien::Leased(b), liens_b)) => (&env, &flow))
        )

        (
            (if a == b)!
            (liens_covered_by(liens_a, liens_b) => ())
            --------------------------- ("l-l")
            (sub_liens(env, flow, Cons(Lien::Var(a), liens_a), Cons(Lien::Var(b), liens_b)) => (&env, &flow))
        )
    }
}

judgment_fn! {
    fn liens_covered_by(
        a: Liens,
        b: Liens,
    ) => () {
        debug(a, b)

        (
            (liens_covered_by(liens_a, liens_b) => ())
            ------------------------------- ("skip lease prefix")
            (liens_covered_by(Cons(Lien::Leased(_), liens_a), liens_b) => ())
        )

        (
            (liens_strictly_covered_by(liens_a, liens_b) => ())
            ------------------------------- ("strictly covered")
            (liens_covered_by(liens_a, liens_b) => ())
        )
    }
}

judgment_fn! {
    fn liens_strictly_covered_by(
        a: Liens,
        b: Liens,
    ) => () {
        debug(a, b)

        (
            ------------------------------- ("my-my")
            (liens_strictly_covered_by(My(), My()) => ())
        )

        (
            (if place_covered_by_place(&a, &b))
            (liens_strictly_covered_by(liens_a, liens_b) => ())
            ------------------------------- ("lease-lease")
            (liens_strictly_covered_by(Cons(Lien::Leased(a), liens_a), Cons(Lien::Leased(b), liens_b)) => ())
        )

        (
            (if a == b)
            (liens_strictly_covered_by(liens_a, liens_b) => ())
            ------------------------------- ("var-var")
            (liens_strictly_covered_by(Cons(Lien::Var(a), liens_a), Cons(Lien::Var(b), liens_b)) => ())
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

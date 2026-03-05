use formality_core::judgment_fn;
use itertools::izip;

use crate::{
    grammar::{ty_impls::PermTy, NamedTy, Parameter, Perm, Ty, VarianceKind},
    type_system::{
        env::Env,
        liveness::LivePlaces,
        predicates::{prove_is_copy, prove_is_owned},
        redperms::sub_perms,
    },
};

judgment_fn! {
    /// Provable if `a` is an instance of `b` with some permission (any permission).
    ///
    /// Equivalent to, in Dada surface syntax, what would allow you to call a
    /// function like `fn foo(x: Bar)`, which is desugared to `fn foo[perm P](x: P Bar)`.
    /// i.e., a `Bar` with *some* permission, any permission.
    pub fn sub_named_ty(
        env: Env,
        live_after: LivePlaces,
        a: Ty,
        b: NamedTy,
    ) => Perm {
        debug(a, b, live_after, env)

        (
            (if let Ty::NamedTy(ty_a) = ty_a)
            (if ty_a.name == ty_b.name)!
            (sub(env, live_after, PermTy::new(&perm_a, ty_a), PermTy::new(&perm_a, ty_b)) => ())
            ------------------------------- ("sub-classes")
            (sub_named_ty(env, live_after, PermTy(perm_a, ty_a), ty_b) => perm_a.clone())
        )
    }
}

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
            // These two ought to be equivalent
            (sub_perms(env, live_after, perm_a, perm_b) => ())
            ------------------------------- ("sub-perms")
            (sub(env, live_after, perm_a: Perm, perm_b: Perm) => ())
        )

        (
            (if var_a == var_b)!
            (sub_perms(env, live_after, perm_a, perm_b) => ())
            ------------------------------- ("sub-eq-vars")
            (sub(env, live_after, PermTy(perm_a, Ty::Var(var_a)), PermTy(perm_b, Ty::Var(var_b))) => ())
        )

        // For shared classes, permissions distribute into the type parameters:
        // `A SharedClass[B] <: X SharedClass[Y]` if `A B <: X Y`.
        // Permissions on a shared class with no parameters (e.g. Int) are vacuously equal.
        (
            (if let Ty::NamedTy(NamedTy { name: name_a, parameters: parameters_a }) = ty_a)
            (if let Ty::NamedTy(NamedTy { name: name_b, parameters: parameters_b }) = ty_b)
            (if name_a == name_b)
            (if let true = env.is_shared_ty(&name_a)?)!
            (if parameters_a.len() == parameters_b.len())
            (for_all(pair in parameters_a.iter().zip(parameters_b))
                (let (pa, pb) = pair)
                (sub(env, live_after, perm_a.apply_to_parameter(pa), perm_b.apply_to_parameter(pb)) => ()))
            ------------------------------- ("sub-shared-classes")
            (sub(env, live_after, PermTy(perm_a, ty_a), PermTy(perm_b, ty_b)) => ())
        )

        (
            (if let Ty::NamedTy(NamedTy { name: name_a, parameters: parameters_a }) = ty_a)
            (if let Ty::NamedTy(NamedTy { name: name_b, parameters: parameters_b }) = ty_b)
            (if name_a == name_b)!
            (sub_perms(env, live_after, perm_a, perm_b) => ())
            (let variances = env.variances(&name_a)?)
            (if parameters_a.len() == variances.len())
            (if parameters_b.len() == variances.len())
            (for_all(triple in izip!(variances, parameters_a, parameters_b))
                (let (v, pa, pb) = triple)
                (sub_generic_parameter(env, live_after, v, perm_a, pa, perm_b, pb) => ()))
            ------------------------------- ("sub-classes")
            (sub(env, live_after, PermTy(perm_a, ty_a), PermTy(perm_b, ty_b)) => ())
        )
    }
}

judgment_fn! {
    fn sub_generic_parameter(
        env: Env,
        live_after: LivePlaces,
        variances: Vec<VarianceKind>,
        perm_a: Perm,
        a: Parameter,
        perm_b: Perm,
        b: Parameter,
    ) => () {
        debug(perm_a, a, perm_b, b, variances, live_after, env)

        // invariant is always ok

        (
            (sub(env, live_after, a, b) => ())
            (sub(env, live_after, b, a) => ())
            ------------------------------- ("invariant")
            (sub_generic_parameter(env, live_after, _v, _perm_a, a, _perm_b, b) => ())
        )

        // We want to allow covariant unless the values are leased.
        // We do that by allowing it if the target type is `copy` or `my`.
        //
        // Here we rule out any form of variance (relative, atomic) and
        // limit that to invariant. This is stricter than needed.

        (
            (prove_is_copy(env, perm_b) => ())
            (sub(env, live_after, perm_a.apply_to_parameter(a), perm_b.apply_to_parameter(b)) => ())
            ------------------------------- ("covariant-copy")
            (sub_generic_parameter(env, live_after, (), perm_a, a, perm_b, b) => ())
        )

        (
            (prove_is_owned(env, perm_b) => ())
            (sub(env, live_after, perm_a.apply_to_parameter(a), perm_b.apply_to_parameter(b)) => ())
            ------------------------------- ("covariant-owned")
            (sub_generic_parameter(env, live_after, (), perm_a, a, perm_b, b) => ())
        )
    }
}

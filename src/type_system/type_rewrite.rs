use formality_core::{judgment_fn, Cons, Downcast};

use crate::{
    grammar::{NamedTy, Parameter, Perm, Ty},
    type_system::{
        env::Env,
        type_subtype::{is_leased, is_mine, is_shared},
    },
};

judgment_fn! {
    /// Produces equivalent versions of a type, primarily by simplifying permissions.
    /// For example a `shared(a) shared(b) String` is equivalent to a `shared(b) String`,
    /// and a `leased(a) leased(b) String` is equivalent to a `leased(a) String`.
    /// Does in some case introduce permisions, e.g. the class type `Foo` and
    /// `given{} Foo` are equivalent.
    pub fn equivalent(
        env: Env,
        a: Ty,
    ) => (Env, Ty) {
        debug(a, env)

        (
            ---------------------- ("identity")
            (equivalent(env, p) => (env, p))
        )

        (
            ---------------------- ("identity")
            (equivalent(env, c: NamedTy) => (env, Ty::apply_perm(Perm::My, c)))
        )

        (
            (is_shared(env, &p) => env)
            (shared_equivalent(env, &p, &*a) => (env, b))
            ---------------------- ("(_ shared) => shared")
            (equivalent(env, Ty::ApplyPerm(p, a)) => (env, b.downcast::<Ty>().unwrap()))
        )

        (
            (equivalent(env, &*a) => (env, b))
            (is_shared(env, &b) => env)
            ---------------------- ("(_ shared) => shared")
            (equivalent(env, Ty::ApplyPerm(_, a)) => (env, &b))
        )

        (
            (is_leased(env, &p) => env)
            (equivalent(env, &*a) => (env, b))
            (if let Some(Ty::ApplyPerm(q, b)) = b.downcast())
            (is_leased(env, q) => env)
            ---------------------- ("(leased(a) leased(b)) => leased(a)")
            (equivalent(env, Ty::ApplyPerm(p, a)) => (env, Ty::apply_perm(&p, &*b)))
        )

        (
            (is_mine(env, &p) => env)
            (equivalent(env, &*a) => (env, b))
            ---------------------- ("(given() owned) => owned")
            (equivalent(env, Ty::ApplyPerm(p, a)) => (env, b))
        )
    }
}

judgment_fn! {
    fn shared_equivalent(
        env: Env,
        shared_perm: Perm,
        a: Parameter,
    ) => (Env, Parameter) {
        debug(shared_perm, a, env)

        (
            (shared_equivalent_all(env, &shared_perm, parameters) => (env, parameters))
            ---------------------- ("class types")
            (shared_equivalent(env, shared_perm, NamedTy { name, parameters }) => (env, Ty::apply_perm(&shared_perm, NamedTy::new(&name, parameters))))
        )

        (
            ---------------------- ("variable types")
            (shared_equivalent(env, shared_perm, var @ Ty::Var(_)) => (env, Ty::apply_perm(&shared_perm, var)))
        )

        (
            ---------------------- ("my permission")
            (shared_equivalent(env, shared_perm, Perm::My) => (env, shared_perm))
        )

        (
            (is_shared(env, &perm) => env)
            ---------------------- ("shared permissions")
            (shared_equivalent(env, _shared_perm, perm) => (env, &perm))
        )

        (
            ---------------------- ("leased permissions")
            (shared_equivalent(env, _shared_perm, Perm::Leased(places)) => (env, Perm::ShLeased(places)))
        )

        // FIXME: permission variables?
        // FIXME: given permissions?
    }
}

judgment_fn! {
    fn shared_equivalent_all(
        env: Env,
        shared_perm: Perm,
        a: Vec<Parameter>,
    ) => (Env, Vec<Parameter>) {
        debug(shared_perm, a, env)

        (
            ---------------------- ("nil")
            (shared_equivalent_all(env, _shared_perm, ()) => (env, ()))
        )

        (
            (shared_equivalent(env, &shared_perm, p_head) => (env, p_head))
            (shared_equivalent_all(env, &shared_perm, &p_tail) => (env, p_tail))
            ---------------------- ("cons")
            (shared_equivalent_all(env, shared_perm, Cons(p_head, p_tail)) => (env, Cons(&p_head, p_tail)))
        )
    }
}

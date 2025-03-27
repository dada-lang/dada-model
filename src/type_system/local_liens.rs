use formality_core::{judgment_fn, term, Set};

use crate::{
    grammar::{NamedTy, Parameter, Perm, Place, Ty},
    type_system::{env::Env, quantifiers::collect},
};

/// A lien on some data local to the current function.
/// This is a subset of the full [`Perm`] type that only
/// contains those variants relative to borrow checking.
#[term]
pub enum Lien {
    Shared(Place),
    Leased(Place),
}

judgment_fn! {
    /// Compute the liens required for a parameter `a` to be valid.
    pub fn liens(
        env: Env,
        a: Parameter,
    ) => Set<Lien> {
        debug(a, env)

        (
            (collect(some_lien(&env, a)) => liens)
            ----------------------------------- ("my")
            (liens(env, a) => liens)
        )
    }
}

judgment_fn! {
    /// The `some_lien` judgment indicate all the ways that a lien
    /// can be derived from a [`Parameter`][]. This rule is a bit
    /// different than others in that it is used with `collect`, so if things
    /// are missing here, the result will be unsound (permission check won't
    /// enforce the lien).
    fn some_lien(
        env: Env,
        a: Parameter,
    ) => Lien {
        debug(a, env)

        (
            (places => place)
            ----------------------------------- ("shared")
            (some_lien(_env, Perm::Shared(places)) => Lien::shared(&place))
        )

        (
            (places => place)
            ----------------------------------- ("leased")
            (some_lien(_env, Perm::Leased(places)) => Lien::leased(&place))
        )

        (
            (places => place)
            (let place_ty = env.place_ty(&place)?)
            (some_lien(&env, place_ty) => lien)
            ----------------------------------- ("place type")
            (some_lien(env, Perm::Shared(places) | Perm::Leased(places) | Perm::Given(places)) => lien)
        )

        (
            (parameters => parameter)
            (some_lien(&env, parameter) => lien)
            ----------------------------------- ("named")
            (some_lien(_env, Ty::NamedTy(NamedTy { name: _, parameters })) => lien)
        )

        (
            (some_lien(env, &*lhs) => lien)
            ----------------------------------- ("perm-lhs")
            (some_lien(env, Perm::Apply(lhs, _rhs)) => lien)
        )

        (
            (some_lien(env, &*rhs) => lien)
            ----------------------------------- ("perm-rhs")
            (some_lien(env, Perm::Apply(_lhs, rhs)) => lien)
        )

        (
            (some_lien(&env, perm) => lien)
            ----------------------------------- ("apply-perm-perm")
            (some_lien(_env, Ty::ApplyPerm(perm, _)) => lien)
        )

        (
            (some_lien(&env, &*ty) => lien)
            ----------------------------------- ("apply-perm-ty")
            (some_lien(_env, Ty::ApplyPerm(_, ty)) => lien)
        )
    }
}

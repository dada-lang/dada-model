use formality_core::{judgment_fn, set, term, Set};

use crate::{
    grammar::{NamedTy, Parameter, Perm, Place, Variable},
    type_system::{
        env::Env,
        quantifiers::union,
        red_terms::{red_term, RedPerm, RedTerm, RedTy},
    },
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
    pub fn liens(
        env: Env,
        a: Parameter,
    ) => Set<Lien> {
        debug(a, env)

        (
            (red_term(&env, a) => RedTerm { red_perm, red_ty })
            (liens_from_red_perm(&env, red_perm) => liens_1)
            (liens_from_red_ty(&env, &red_ty) => liens_2)
            ----------------------------------- ("my")
            (liens(env, a) => (&liens_1, liens_2))
        )
    }
}

judgment_fn! {
    fn liens_from_red_ty(
        env: Env,
        a: RedTy,
    ) => Set<Lien> {
        debug(a, env)

        (
            ----------------------------------- ("none")
            (liens_from_red_ty(_env, RedTy::None) => ())
        )

        (
            ----------------------------------- ("var")
            (liens_from_red_ty(_env, RedTy::Var(_var)) => ())
        )

        (
            (union(parameters, &|parameter| liens(&env, parameter)) => liens)
            ----------------------------------- ("named")
            (liens_from_red_ty(_env, RedTy::NamedTy(NamedTy { name: _, parameters })) => liens)
        )
    }
}

judgment_fn! {
    fn liens_from_red_perm(
        env: Env,
        a: RedPerm,
    ) => Set<Lien> {
        debug(a, env)

        (
            (union(perms, &|perm| liens_from_perm(&env, perm)) => liens_out)
            ----------------------------------- ("none")
            (liens_from_red_perm(_env, RedPerm { perms }) => liens_out)
        )
    }
}

judgment_fn! {
    fn liens_from_perm(
        env: Env,
        a: Perm,
    ) => Set<Lien> {
        debug(a, env)

        (
            ----------------------------------- ("none")
            (liens_from_perm(_env, Perm::Our | Perm::Var(Variable::UniversalVar(_))) => ())
        )

        (
            (places => place)
            (let place_ty = env.place_ty(&place)?)
            (liens(&env, place_ty) => liens)
            ----------------------------------- ("shared")
            (liens_from_perm(_env, Perm::Shared(places)) => set![Lien::shared(&place), ..liens])
        )

        (
            (places => place)
            (let place_ty = env.place_ty(&place)?)
            (liens(&env, place_ty) => liens)
            ----------------------------------- ("leased")
            (liens_from_perm(_env, Perm::Leased(places)) => set![Lien::leased(&place), ..liens])
        )

        (
            (places => place)
            (let place_ty = env.place_ty(&place)?)
            (liens(&env, place_ty) => liens)
            ----------------------------------- ("shared")
            (liens_from_perm(_env, Perm::Given(places)) => liens)
        )
    }
}

use std::sync::Arc;

use formality_core::{cast_impl, judgment_fn, Cons, Downcast, DowncastFrom, Upcast};

use crate::{
    grammar::{NamedTy, Parameter, Perm, Ty, UniversalVar, Variable},
    type_system::predicates::{prove_is_copy, MeetsPredicate},
};

use super::env::Env;

/// "Red(uced) terms" are derived from user [`Parameter`][] terms
/// and represent the final, reduced form of a permission or type.
/// There is a single unified format for all [kinds](`crate::dada_lang::ParameterKind`)
/// of [`Parameter`][] terms. All terms are reduced to a [`RedPerms`][] and a [`RedTy`][],
/// with parameters of kind [`ParameterKind::Perm`][] being represented
/// using [`RedTy::None`][].
#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct RedTerm {
    pub red_perm: RedPerm,
    pub red_ty: RedTy,
}

cast_impl!(RedTerm);

/// "Red(uced) types" are derived from user [`Ty`][] terms
/// and represent the core type of the underlying value.
/// Unlike [`Ty`][] however they represent only the type itself
/// and not the permissions on that type-- the full info is captured
/// in the [`RedTerm`][] that is created from the [`Ty`][].
/// Another wrinkle is that [`RedTy`][] values can be created from
/// any generic term, including permissions, in which case the
/// [`RedTy`] variant is [`RedTy::None`].
#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum RedTy {
    /// Generic type variable.
    Var(UniversalVar),

    /// Named type.
    NamedTy(NamedTy),

    /// No data at all -- this occurs when we ask for the "lien data" of a permission.
    None,
}

cast_impl!(RedTy);
cast_impl!(RedTy::Var(UniversalVar));
cast_impl!(RedTy::NamedTy(NamedTy));

/// "Red(uced) perms" are derived from the [`Perm`][] terms
/// written by users. They indicate the precise implications
/// of a permission. Many distinct [`Perm`][] terms can
/// be reduced to the same `RedPerms`. For example:
///
/// * `leased[d1] our` and `our` are equivalent;
/// * `leased[d1] leased[d2]` and `leased[d1, d2]` are equivalent;
/// * and so forth.
///
/// In thinking about red-perms it is helpful to remember
/// the permission matrix:
///
/// |         | `move`       | `copy`                          |
/// |---------|--------------|---------------------------------|
/// | `owned` | `my`         | `our`                           |
/// | `lent`  | `leased[..]` | `shared[..]`,  `our leased[..]` |
///
/// All red perms represent something in this matrix (modulo generics).
#[derive(Clone, Debug, Default, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct RedPerm {
    /// Invariant: no perm in this vector is `My` nor `Apply`
    pub perms: Vec<Perm>,
}

cast_impl!(RedPerm);

impl RedPerm {
    pub fn my() -> Self {
        RedPerm { perms: vec![] }
    }

    pub fn our() -> Self {
        RedPerm::leaf(Perm::Our)
    }

    pub fn leaf(perm: impl Upcast<Perm>) -> Self {
        let perm: Perm = perm.upcast();
        match perm {
            Perm::My => RedPerm::my(),
            Perm::Apply(..) => panic!("not a leaf"),
            _ => RedPerm { perms: vec![perm] },
        }
    }

    /// Concatenate the perms from `self` and the perms from `other`
    fn concat(&self, _env: &Env, other: impl Upcast<RedPerm>) -> RedPerm {
        let mut this = self.clone();
        let other: RedPerm = other.upcast();
        this.perms.extend(other.perms);
        this
    }
}

impl Upcast<Perm> for RedPerm {
    fn upcast(mut self) -> Perm {
        if self.perms.len() == 0 {
            Perm::My
        } else if self.perms.len() == 1 {
            self.perms.pop().unwrap()
        } else {
            let mut perms = self.perms.into_iter();
            let perm0 = perms.next().unwrap();
            perms.fold(perm0, Perm::apply)
        }
    }
}

impl Upcast<Arc<Perm>> for RedPerm {
    fn upcast(self) -> Arc<Perm> {
        let perm: Perm = self.upcast();
        Arc::new(perm)
    }
}

impl Upcast<Parameter> for RedPerm {
    fn upcast(self) -> Parameter {
        let perm: Perm = self.upcast();
        perm.upcast()
    }
}

impl Upcast<Arc<Parameter>> for RedPerm {
    fn upcast(self) -> Arc<Parameter> {
        let perm: Parameter = self.upcast();
        Arc::new(perm)
    }
}

impl<C> DowncastFrom<RedPerm> for Cons<Perm, C>
where
    C: DowncastFrom<RedPerm>,
{
    fn downcast_from(chain: &RedPerm) -> Option<Self> {
        let Some((first, rest)) = chain.perms.split_first() else {
            return None;
        };

        let rest_chain = RedPerm {
            perms: rest.to_vec(),
        };
        let rest = rest_chain.downcast::<C>()?;

        Some(Cons(first.clone(), rest))
    }
}

judgment_fn! {
    pub fn red_term(
        env: Env,
        a: Parameter,
    ) => RedTerm {
        debug(a, env)

        (
            (red_term_under(env, Perm::My, a) => red_term)
            ----------------------------------- ("red term")
            (red_term(env, a) => red_term)
        )
    }
}

judgment_fn! {
    pub fn red_term_under(
        env: Env,
        perm: Perm,
        a: Parameter,
    ) => RedTerm {
        debug(perm, a, env)

        (
            (red_ty(&env, &a) => (perm_a, red_ty))
            (red_perm(&env, Perm::apply(&perm_u, perm_a)) => red_perm)
            ----------------------------------- ("red term")
            (red_term_under(env, perm_u, a) => RedTerm { red_perm, red_ty: red_ty.clone() })
        )
    }
}

judgment_fn! {
    fn red_ty(
        env: Env,
        a: Parameter,
    ) => (Perm, RedTy) {
        debug(a, env)

        (
            ----------------------------------- ("perm")
            (red_ty(_env, a: Perm) => (a, RedTy::None))
        )

        (
            (red_ty(&env, &*ty_r) => (perm_r, red_ty_r))
            (let perm_lr = Perm::apply(&perm_l, perm_r))
            ----------------------------------- ("ty-apply")
            (red_ty(env, Ty::ApplyPerm(perm_l, ty_r)) => (perm_lr, red_ty_r))
        )

        (
            ----------------------------------- ("universal ty var")
            (red_ty(_env, Ty::Var(Variable::UniversalVar(v))) => (Perm::My, RedTy::Var(v)))
        )

        (
            ----------------------------------- ("named ty")
            (red_ty(_env, Ty::NamedTy(n)) => (Perm::My, RedTy::NamedTy(n)))
        )
    }
}

judgment_fn! {
    pub fn red_perm(
        env: Env,
        a: Perm,
    ) => RedPerm {
        debug(a, env)

        (
            ----------------------------------- ("my")
            (red_perm(_env, Perm::My) => RedPerm::leaf(Perm::My))
        )

        (
            ----------------------------------- ("our")
            (red_perm(_env, Perm::Our) => RedPerm::leaf(Perm::Our))
        )

        (
            ----------------------------------- ("shared")
            (red_perm(_env, perm @ Perm::Shared(_)) => RedPerm::leaf(perm))
        )

        (
            ----------------------------------- ("leased")
            (red_perm(_env, perm @ Perm::Leased(_)) => RedPerm::leaf(perm))
        )

        (
            // XXX this may be right but something is wrong
            ----------------------------------- ("given")
            (red_perm(_env, perm @ Perm::Given(_)) => RedPerm::leaf(perm))
        )

        (
            ----------------------------------- ("var")
            (red_perm(_env, perm @ Perm::Var(_)) => RedPerm::leaf(perm))
        )

        (
            (if let false = r.is_copy(&env)?)
            (red_perm(&env, &*l) => red_perm_l)
            (red_perm(&env, &*r) => red_perm_r)
            ----------------------------------- ("perm-apply")
            (red_perm(env, Perm::Apply(l, r)) => red_perm_l.concat(&env, red_perm_r))
        )

        (
            (if let true = r.is_copy(&env)?)
            (red_perm(&env, &*r) => red_perm_r)
            ----------------------------------- ("perm-apply-copy")
            (red_perm(env, Perm::Apply(_l, r)) => red_perm_r)
        )
    }
}

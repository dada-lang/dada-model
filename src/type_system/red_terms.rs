use formality_core::{cast_impl, judgment_fn, Cons, Downcast, DowncastFrom, Fallible, Set, Upcast};

use crate::{
    grammar::{NamedTy, Parameter, ParameterPredicate, Perm, Place, Ty, UniversalVar, Variable},
    type_system::quantifiers::collect,
};

use super::{env::Env, predicates::MeetsPredicate};

/// "Red(uced) terms" are derived from user [`Parameter`][] terms
/// and represent the final, reduced form of a permission or type.
/// There is a single unified format for all [kinds](`crate::dada_lang::ParameterKind`)
/// of [`Parameter`][] terms. All terms are reduced to a [`RedPerms`][] and a [`RedTy`][],
/// with parameters of kind [`ParameterKind::Perm`][] being represented
/// using [`RedTy::None`][].
#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct RedTerm {
    pub ty_chains: Set<TyChain>,
}

cast_impl!(RedTerm);

/// A typed chain (of custody) indicates where the value originates
/// as well as the type of data it contains. Somewhat confusing a [`TyChain`][]
/// can also be constructed from a permission, in which case the type is
/// [`RedTy::None`].
#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct TyChain {
    pub chain: Chain,
    pub ty: RedTy,
}

cast_impl!(TyChain);

impl TyChain {
    pub fn is_copy(&self, env: &Env) -> Fallible<bool> {
        Ok(self.chain.is_copy(env) || self.ty.is_copy(env)?)
    }
}

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

impl RedTy {
    pub fn is_copy(&self, env: &Env) -> Fallible<bool> {
        match self {
            RedTy::Var(v) => v.meets_predicate(env, ParameterPredicate::Copy),
            RedTy::NamedTy(n) => n.meets_predicate(env, ParameterPredicate::Copy),
            RedTy::None => Ok(false),
        }
    }
}

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
    chains: Set<Chain>,
}

cast_impl!(RedPerm);

/// A chain (of custody) indicates where the value originates.
#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct Chain {
    pub liens: Vec<Lien>,
}

cast_impl!(Chain);

impl Chain {
    pub fn my() -> Chain {
        Chain { liens: vec![] }
    }

    pub fn our() -> Chain {
        Chain {
            liens: vec![Lien::Our],
        }
    }

    pub fn shared(place: impl Upcast<Place>) -> Chain {
        Chain {
            liens: vec![Lien::Shared(place.upcast())],
        }
    }

    pub fn leased(place: impl Upcast<Place>) -> Chain {
        Chain {
            liens: vec![Lien::Leased(place.upcast())],
        }
    }

    pub fn var(v: impl Upcast<UniversalVar>) -> Chain {
        Chain {
            liens: vec![Lien::Variable(v.upcast())],
        }
    }

    /// Create a new chain of custody `(self other)`.
    pub fn concat(&self, env: &Env, other: impl Upcast<Chain>) -> Chain {
        let other: Chain = other.upcast();
        if other.is_copy(env) {
            other
        } else {
            Chain {
                liens: self.liens.iter().chain(&other.liens).cloned().collect(),
            }
        }
    }

    pub fn concat_term(&self, env: &Env, other: impl Upcast<RedTerm>) -> Fallible<RedTerm> {
        let other: RedTerm = other.upcast();
        let mut ty_chains = Set::new();
        for ty_chain in &other.ty_chains {
            ty_chains.insert(self.concat_ty(&env, ty_chain)?);
        }
        Ok(RedTerm { ty_chains })
    }

    /// Create a new typed chain of custody `(self other)`.
    pub fn concat_ty(&self, env: &Env, other: impl Upcast<TyChain>) -> Fallible<TyChain> {
        let other: TyChain = other.upcast();
        if other.is_copy(env)? {
            Ok(other)
        } else {
            Ok(TyChain {
                chain: self.concat(&env, &other.chain),
                ty: other.ty,
            })
        }
    }

    pub fn is_copy(&self, env: &Env) -> bool {
        self.liens.iter().any(|lien| lien.is_copy(env))
    }

    pub fn is_moved(&self, env: &Env) -> bool {
        self.liens.iter().all(|lien| lien.is_moved(env))
    }

    pub fn is_lent(&self, env: &Env) -> bool {
        self.liens.iter().any(|lien| lien.is_lent(env))
    }

    pub fn is_owned(&self, env: &Env) -> bool {
        self.liens.iter().all(|lien| lien.is_owned(env))
    }

    pub fn is_leased(&self, env: &Env) -> bool {
        self.liens
            .iter()
            .any(|lien| lien.is_lent(env) && lien.is_moved(env))
    }
}

impl<C> DowncastFrom<Chain> for Cons<Lien, C>
where
    C: DowncastFrom<Chain>,
{
    fn downcast_from(chain: &Chain) -> Option<Self> {
        let Some((first, rest)) = chain.liens.split_first() else {
            return None;
        };

        let rest_chain = Chain {
            liens: rest.to_vec(),
        };
        let rest = rest_chain.downcast::<C>()?;

        Some(Cons(first.clone(), rest))
    }
}

/// A lien is part of a [chain of custody](`Chain`).
#[derive(Clone, Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum Lien {
    Our,
    Shared(Place),
    Leased(Place),
    Variable(UniversalVar),
}

cast_impl!(Lien);
impl Lien {
    pub fn is_copy(&self, env: &Env) -> bool {
        match self {
            Lien::Our | Lien::Shared(_) => true,
            Lien::Leased(_) => false,
            Lien::Variable(var) => env.assumed_to_meet(var, ParameterPredicate::Copy),
        }
    }

    pub fn is_moved(&self, env: &Env) -> bool {
        match self {
            Lien::Our | Lien::Shared(_) => false,
            Lien::Leased(_) => true,
            Lien::Variable(var) => env.assumed_to_meet(var, ParameterPredicate::Move_),
        }
    }

    pub fn is_lent(&self, env: &Env) -> bool {
        match self {
            Lien::Our => false,
            Lien::Shared(_) | Lien::Leased(_) => true,
            Lien::Variable(var) => env.assumed_to_meet(var, ParameterPredicate::Lent),
        }
    }

    pub fn is_owned(&self, env: &Env) -> bool {
        match self {
            Lien::Our => true,
            Lien::Shared(_) | Lien::Leased(_) => false,
            Lien::Variable(var) => env.assumed_to_meet(var, ParameterPredicate::Owned),
        }
    }
}

judgment_fn! {
    pub fn red_term_under(
        env: Env,
        chain: Chain,
        a: Parameter,
    ) => RedTerm {
        debug(chain, a, env)

        (
            (red_term(&env, a) => red_term)
            (let red_term = chain.concat_term(&env, red_term)?)
            ----------------------------------- ("red term")
            (red_term_under(env, chain, a) => red_term)
        )
    }
}

judgment_fn! {
    pub fn red_term(
        env: Env,
        a: Parameter,
    ) => RedTerm {
        debug(a, env)

        (
            (collect(ty_chain_of_custody(env, a)) => ty_chains)
            ----------------------------------- ("red term")
            (red_term(env, a) => RedTerm { ty_chains })
        )

    }
}

judgment_fn! {
    fn ty_chain_of_custody(
        env: Env,
        a: Parameter,
    ) => TyChain {
        debug(a, env)

        (
            (chain_of_custody(&env, a) => chain)
            ----------------------------------- ("perm")
            (ty_chain_of_custody(env, _a: Perm) => TyChain { chain, ty: RedTy::None })
        )

        (
            (chain_of_custody(&env, l) => chain_l)
            (ty_chain_of_custody(&env, &*r) => chain_r)
            (let chain_l_r = chain_l.concat_ty(&env, chain_r)?)
            ----------------------------------- ("ty-apply")
            (ty_chain_of_custody(env, Ty::ApplyPerm(l, r)) => chain_l_r)
        )

        (
            ----------------------------------- ("universal ty var")
            (ty_chain_of_custody(_env, Ty::Var(Variable::UniversalVar(v))) => TyChain { chain: Chain::my(), ty: RedTy::Var(v) })
        )

        (
            ----------------------------------- ("named ty")
            (ty_chain_of_custody(_env, Ty::NamedTy(n)) => TyChain { chain: Chain::my(), ty: RedTy::NamedTy(n) })
        )
    }
}

judgment_fn! {
    pub fn red_perm(
        env: Env,
        a: Parameter,
    ) => RedPerm {
        debug(a, env)

        (
            (collect(chain_of_custody(env, a)) => chains)
            ----------------------------------- ("my")
            (red_perm(env, a) => RedPerm { chains })
        )

    }
}

judgment_fn! {
    fn chain_of_custody(
        env: Env,
        a: Parameter,
    ) => Chain {
        debug(a, env)

        (
            ----------------------------------- ("my")
            (chain_of_custody(_env, Perm::My) => Chain::my())
        )

        (
            ----------------------------------- ("our")
            (chain_of_custody(_env, Perm::Our) => Chain::our())
        )

        (
            (&places => place)
            (let place_ty = env.place_ty(&place)?)
            (chain_of_custody(&env, place_ty) => chain)
            ----------------------------------- ("shared")
            (chain_of_custody(env, Perm::Shared(places)) => Chain::shared(&place).concat(&env, chain))
        )

        (
            (&places => place)
            (let place_ty = env.place_ty(&place)?)
            (chain_of_custody(&env, place_ty) => chain)
            ----------------------------------- ("leased")
            (chain_of_custody(env, Perm::Leased(places)) => Chain::leased(&place).concat(&env, chain))
        )

        (
            (&places => place)
            (let place_ty = env.place_ty(&place)?)
            (chain_of_custody(&env, place_ty) => chain)
            ----------------------------------- ("given")
            (chain_of_custody(env, Perm::Given(places)) => chain)
        )

        (
            ----------------------------------- ("universal var")
            (chain_of_custody(_env, v: UniversalVar) => Chain::var(v))
        )

        (
            (chain_of_custody(&env, &*l) => chain_l)
            (chain_of_custody(&env, &*r) => chain_r)
            ----------------------------------- ("perm-apply")
            (chain_of_custody(env, Perm::Apply(l, r)) => chain_l.concat(&env, chain_r))
        )

        (
            (chain_of_custody(&env, l) => chain_l)
            (chain_of_custody(&env, &*r) => chain_r)
            ----------------------------------- ("ty-apply")
            (chain_of_custody(env, Ty::ApplyPerm(l, r)) => chain_l.concat(&env, chain_r))
        )

        (
            ----------------------------------- ("named ty")
            (chain_of_custody(_env, Ty::NamedTy(_n)) => Chain::my())
        )
    }
}

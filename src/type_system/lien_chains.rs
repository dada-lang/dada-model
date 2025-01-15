use formality_core::{
    cast_impl, judgment_fn, set, Cons, Downcast, DowncastTo, Set, Upcast, UpcastFrom,
};

use crate::{
    dada_lang::grammar::{UniversalVar, Variable},
    grammar::{Kind, NamedTy, Parameter, Perm, Place, Ty},
    type_system::{env::Env, places::place_ty},
};

/// A *type chain* pairs up the type of the value with its [`LienChain`][].
#[derive(Clone, PartialOrd, Ord, PartialEq, Eq, Debug, Hash)]
pub enum TyChain {
    Var(LienChain, UniversalVar),
    ClassTy(LienChain, NamedTy),
    ValueTy(LienChain, NamedTy),
}

cast_impl!(TyChain);

/// A *lien chain* indicates the "history" of the liens on a given object.
/// For example `shared{x} leased[y]` means that the object was leased from `y`
/// and then the leased value was shared from `x`.
///
/// Due to subtyping, lien chains may be *incomplete*, in which they are
/// missing some elements in the middle. e.g. `shared(x) leased(y) my` is a
/// subchain of `shared(x) my`. Inuitively, this is ok because the type of `x`
/// still holds the lease on `y`.
///
/// Lien chains are computed by the `ty_chains` and `lien_chains`
/// judgments.
#[derive(Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct LienChain {
    pub vec: Vec<Lien>,
}

cast_impl!(LienChain);

#[derive(Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum Lien {
    Our,
    Shared(Place),
    Leased(Place),
    Var(UniversalVar),
}

cast_impl!(Lien);

impl Lien {
    fn covers(&self, other: &Self) -> bool {
        match (self, other) {
            (Lien::Shared(p), Lien::Shared(q)) => p.is_prefix_of(q),
            (Lien::Shared(_), _) | (_, Lien::Shared(_)) => false,
            (Lien::Leased(p), Lien::Leased(q)) => p.is_prefix_of(q),
            (Lien::Leased(_), _) | (_, Lien::Leased(_)) => false,
            (Lien::Var(v), Lien::Var(w)) => v == w,
            (Lien::Var(_), _) | (_, Lien::Var(_)) => false,
            (Lien::Our, Lien::Our) => true,
        }
    }
}

#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Debug, Hash)]
pub struct My();

#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Debug, Hash)]
pub struct Our();

impl LienChain {
    /// Return a new chain with all members of `liens` applied to `self` via [`Self::apply`][].
    fn apply_all(&self, env: &Env, liens: LienChain) -> Self {
        let mut this = self.clone();
        for lien in liens.vec {
            this = this.apply(env, lien);
        }
        this
    }

    /// Returns a new chain equal to `self` with `lien` appended;
    /// if `lien` is shared, this will disregard existing members in `self`.
    fn apply(&self, env: &Env, lien: Lien) -> Self {
        let lien_is_shared = match &lien {
            Lien::Our => true,
            Lien::Shared(_) => true,
            Lien::Var(v) => env.is_copy(v),
            Lien::Leased(_) => false,
        };

        if lien_is_shared {
            LienChain { vec: vec![lien] }
        } else {
            LienChain {
                vec: self.vec.iter().cloned().chain(Some(lien)).collect(),
            }
        }
    }

    /// Adds `lien` to the chain, but first applies all liens in `pending`
    /// that are not covered by `lien`.
    fn apply_lien(&self, env: &Env, lien: Lien, pending: &LienChain) -> (Self, LienChain) {
        let mut this = self.clone();
        let mut pending = pending.vec.iter();

        while let Some(p) = pending.next() {
            if lien.covers(p) {
                break;
            }
            this = this.apply(env, p.clone());
        }

        (
            this.apply(env, lien),
            LienChain {
                vec: pending.cloned().collect(),
            },
        )
    }

    /// Shortcut for [`Self::apply_lien`][] with [`Lien::Var`][].
    fn apply_var(
        &self,
        env: &Env,
        var: impl Upcast<UniversalVar>,
        pending: &LienChain,
    ) -> (Self, LienChain) {
        self.apply_lien(env, Lien::Var(var.upcast()), pending)
    }

    /// Shortcut for [`Self::apply_lien`][] with [`Lien::Leased`][].
    fn apply_leased(
        &self,
        env: &Env,
        place: impl Upcast<Place>,
        pending: &LienChain,
    ) -> (Self, LienChain) {
        self.apply_lien(env, Lien::Leased(place.upcast()), pending)
    }

    /// True if this chain is non-empty (and thus does not necessarily represent unique ownership).
    pub fn is_not_my(&self) -> bool {
        !self.vec.is_empty()
    }
}

impl Lien {
    /// Creates a new [`Lien::Shared`][].
    pub fn shared(place: impl Upcast<Place>) -> Self {
        Self::Shared(place.upcast())
    }

    /// Creates a new [`Lien::Leased`][].
    pub fn leased(place: impl Upcast<Place>) -> Self {
        Self::Leased(place.upcast())
    }
}

impl UpcastFrom<My> for LienChain {
    fn upcast_from(_: My) -> Self {
        Self { vec: vec![] }
    }
}

impl UpcastFrom<Our> for LienChain {
    fn upcast_from(_: Our) -> Self {
        Self {
            vec: vec![Lien::Our],
        }
    }
}

// impl UpcastFrom<Liens> for Perm {
//     fn upcast_from(liens: Liens) -> Self {
//         todo!()
//     }
// }

impl UpcastFrom<Lien> for LienChain {
    fn upcast_from(lien: Lien) -> Self {
        Self { vec: vec![lien] }
    }
}

impl UpcastFrom<Our> for Lien {
    fn upcast_from(_: Our) -> Self {
        Lien::Our
    }
}

impl DowncastTo<My> for LienChain {
    fn downcast_to(&self) -> Option<My> {
        if self.vec.is_empty() {
            Some(My())
        } else {
            None
        }
    }
}

impl DowncastTo<Our> for LienChain {
    fn downcast_to(&self) -> Option<Our> {
        if self.vec.len() == 1 && matches!(self.vec[0], Lien::Our) {
            Some(Our())
        } else {
            None
        }
    }
}

impl DowncastTo<Cons<Lien, LienChain>> for LienChain {
    fn downcast_to(&self) -> Option<Cons<Lien, LienChain>> {
        let Cons(lien, liens) = self.vec.downcast()?;
        Some(Cons(lien, LienChain { vec: liens }))
    }
}

impl<L, C> UpcastFrom<Cons<L, C>> for LienChain
where
    L: Upcast<Lien>,
    C: Upcast<LienChain>,
{
    fn upcast_from(cons: Cons<L, C>) -> Self {
        let Cons(lien, chain) = cons;
        let mut chain: LienChain = chain.upcast();
        chain.vec.insert(0, lien.upcast());
        chain
    }
}

pub fn collapse(env: &Env, pairs: Set<(LienChain, LienChain)>) -> Set<LienChain> {
    pairs
        .into_iter()
        .map(|(a, b)| a.apply_all(env, b))
        .collect()
}

judgment_fn! {
    /// Computes the set of [`TyChain`][]es for a given type.
    pub fn ty_chains(
        env: Env,
        cx: LienChain,
        a: Ty,
    ) => Set<TyChain> {
        debug(cx, a, env)

        (
            (ty_chains_cx(&env, My(), cx, a) => ty_liens)
            ----------------------------------- ("restrictions")
            (ty_chains(env, cx, a) => ty_liens)
        )
    }
}

judgment_fn! {
    /// Computes the set of [`TyChain`][]es for a given type appearing in the context of `chain` and `pending`.
    fn ty_chains_cx(
        env: Env,
        chain: LienChain,
        pending: LienChain,
        a: Ty,
    ) => Set<TyChain> {
        debug(chain, pending, a, env)

        (
            (if env.is_class_ty(&n.name))!
            (let chain = chain.apply_all(&env, pending))
            ----------------------------------- ("named-ty")
            (ty_chains_cx(env, chain, pending, n: NamedTy) => set![TyChain::ClassTy(chain, n)])
        )

        (
            (if env.is_value_ty(&n.name))!
            (let chain = chain.apply_all(&env, pending))
            ----------------------------------- ("named-ty")
            (ty_chains_cx(env, chain, pending, n: NamedTy) => set![TyChain::ValueTy(chain, n)])
        )

        (
            (let chain = chain.apply_all(&env, pending))
            ----------------------------------- ("universal-var")
            (ty_chains_cx(env, chain, pending, v: UniversalVar) => set![TyChain::Var(chain, v)])
        )

        (
            (lien_chain_pairs(&env, chain, pending, perm) => pairs)
            (ty_apply(&env, pairs, &*ty) => ty_chains)
            ----------------------------------- ("apply")
            (ty_chains_cx(env, chain, pending, Ty::ApplyPerm(perm, ty)) => ty_chains)
        )

        (
            (ty_chains_cx(&env, &chain, &pending, &*ty0) => ty_chains0)
            (ty_chains_cx(&env, &chain, &pending, &*ty1) => ty_chains1)
            ----------------------------------- ("or")
            (ty_chains_cx(env, chain, pending, Ty::Or(ty0, ty1)) => (&ty_chains0, ty_chains1))
        )
    }
}

judgment_fn! {
    fn ty_apply(
        env: Env,
        pairs: Set<(LienChain, LienChain)>,
        ty: Ty,
    ) => Set<TyChain> {
        debug(pairs, ty, env)

        (
            -------------------------- ("nil")
            (ty_apply(_env, (), _ty) => ())
        )

        (
            (ty_chains_cx(&env, liens, pending, &ty) => ty_chains0)
            (ty_apply(&env, &pairs, &ty) => ty_chains1)
            -------------------------- ("cons")
            (ty_apply(env, Cons((liens, pending), pairs), ty) => (&ty_chains0, ty_chains1))
        )
    }
}

judgment_fn! {
    pub fn lien_chains(
        env: Env,
        cx: LienChain,
        a: Parameter,
    ) => Set<LienChain> {
        debug(cx, a, env)

        (
            (lien_chain_pairs(&env, My(), cx, a) => pairs)
            ----------------------------------- ("restrictions")
            (lien_chains(env, cx, a) => collapse(&env, pairs))
        )
    }
}

judgment_fn! {
    fn lien_chain_pairs(
        env: Env,
        chain: LienChain,
        pending: LienChain,
        a: Parameter,
    ) => Set<(LienChain, LienChain)> {
        debug(chain, pending, a, env)

        (
            ----------------------------------- ("my")
            (lien_chain_pairs(_env, chain, pending, Perm::My) => set![(chain, pending)])
        )

        (
            ----------------------------------- ("our")
            (lien_chain_pairs(_env, _chain, _pending, Perm::Our) => set![(Our(), My())])
        )

        (
            (given_from_places(&env, chain, pending, places) => pairs)
            ----------------------------------- ("given")
            (lien_chain_pairs(env, chain, pending, Perm::Given(places)) => pairs)
        )

        (
            (shared_from_places(&env, places) => pairs)
            ----------------------------------- ("shared")
            (lien_chain_pairs(env, _chain, _pending, Perm::Shared(places)) => pairs)
        )

        (
            (leased_from_places(&env, chain, pending, places) => pairs)
            ----------------------------------- ("leased")
            (lien_chain_pairs(env, chain, pending, Perm::Leased(places)) => pairs)
        )

        (
            (if var.kind == Kind::Perm)!
            (let pair = chain.apply_var(&env, var, &pending))
            ----------------------------------- ("perm-var")
            (lien_chain_pairs(env, chain, pending, Variable::UniversalVar(var)) => set![pair])
        )

        (
            (if var.kind == Kind::Ty)!
            ----------------------------------- ("ty-var")
            (lien_chain_pairs(_env, chain, pending, Variable::UniversalVar(var)) => set![(chain, pending)])
        )

        (
            (lien_chain_pairs(&env, chain, pending, &*perm0) => pairs)
            (apply(&env, pairs, &*perm1) => pairs)
            ----------------------------------- ("perm-apply")
            (lien_chain_pairs(env, chain, pending, Perm::Apply(perm0, perm1)) => pairs)
        )

        (
            (lien_chain_pairs(&env, chain, pending, perm) => pairs)
            (apply(&env, pairs, &*ty) => pairs)
            ----------------------------------- ("ty-apply")
            (lien_chain_pairs(env, chain, pending, Ty::ApplyPerm(perm, ty)) => pairs)
        )

        (
            (lien_chain_pairs(&env, &chain, &pending, &*perm0) => pairs0)
            (lien_chain_pairs(&env, &chain, &pending, &*perm1) => pairs1)
            ----------------------------------- ("perm-or")
            (lien_chain_pairs(env, chain, pending, Perm::Or(perm0, perm1)) => (&pairs0, pairs1))
        )

        (
            (lien_chain_pairs(&env, &chain, &pending, &*ty0) => pairs0)
            (lien_chain_pairs(&env, &chain, &pending, &*ty1) => pairs1)
            ----------------------------------- ("ty-or")
            (lien_chain_pairs(env, chain, pending, Ty::Or(ty0, ty1)) => (&pairs0, pairs1))
        )

        (
            ----------------------------------- ("named-ty")
            (lien_chain_pairs(_env, chain, pending, NamedTy { .. }) => set![(chain, pending)])
        )
    }
}

fn collapse_to_pending(
    env: &Env,
    chain: impl Upcast<LienChain>,
    pending: impl Upcast<Set<(LienChain, LienChain)>>,
) -> Set<(LienChain, LienChain)> {
    let chain = chain.upcast();
    let pending = pending.upcast();
    pending
        .into_iter()
        .map(|(a, b)| (chain.clone(), a.apply_all(env, b)))
        .collect()
}

judgment_fn! {
    fn given_from_places(
        env: Env,
        chain: LienChain,
        pending: LienChain,
        places: Set<Place>,
    ) => Set<(LienChain, LienChain)> {
        debug(chain, pending, places, env)

        (
            -------------------------- ("nil")
            (given_from_places(_env, _chain, _pending, ()) => ())
        )

        (
            (place_ty(&env, &place) => ty)
            (lien_chain_pairs(&env, My(), &pending, ty) => pairs0)
            (given_from_places(&env, &chain, &pending, &places) => pairs1)
            -------------------------- ("cons")
            (given_from_places(env, chain, pending, Cons(place, places)) => (collapse_to_pending(&env, &chain, &pairs0), pairs1))
        )
    }
}

judgment_fn! {
    fn leased_from_places(
        env: Env,
        chain: LienChain,
        pending: LienChain,
        places: Set<Place>,
    ) => Set<(LienChain, LienChain)> {
        debug(chain, pending, places, env)

        (
            -------------------------- ("nil")
            (leased_from_places(_env, _chain, _pending, ()) => ())
        )

        (
            (place_ty(&env, &place) => ty)
            (let (liens_l, pending_l) = chain.apply_leased(&env, &place, &pending))
            (lien_chain_pairs(&env, My(), &pending_l, ty) => pairs0)
            (leased_from_places(&env, &chain, &pending, &places) => pairs1)
            -------------------------- ("cons")
            (leased_from_places(env, chain, pending, Cons(place, places)) => (collapse_to_pending(&env, &liens_l, &pairs0), pairs1))
        )
    }
}
judgment_fn! {
    fn shared_from_places(
        env: Env,
        places: Set<Place>,
    ) => Set<(LienChain, LienChain)> {
        debug(places, env)

        (
            -------------------------- ("nil")
            (shared_from_places(_env, ()) => ())
        )

        (
            (place_ty(&env, &place) => ty)
            (lien_chain_pairs(&env, My(), My(), ty) => pairs0)
            (shared_from_places(&env, &places) => pairs1)
            -------------------------- ("cons")
            (shared_from_places(env, Cons(place, places)) => (collapse_to_pending(&env, Lien::shared(&place), &pairs0), pairs1))
        )
    }
}

judgment_fn! {
    fn apply(
        env: Env,
        pairs: Set<(LienChain, LienChain)>,
        parameter: Parameter,
    ) => Set<(LienChain, LienChain)> {
        debug(pairs, parameter, env)

        (
            -------------------------- ("nil")
            (apply(_env, (), _parameter) => ())
        )

        (
            (lien_chain_pairs(&env, liens, pending, &parameter) => pairs0)
            (apply(&env, &pairs, &parameter) => pairs1)
            -------------------------- ("cons")
            (apply(env, Cons((liens, pending), pairs), parameter) => (&pairs0, pairs1))
        )
    }
}

impl std::fmt::Debug for LienChain {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.vec.len() == 0 {
            return write!(f, "my");
        }

        let mut prefix = "";
        for lien in &self.vec {
            write!(f, "{}{:?}", prefix, lien)?;
            prefix = " ";
        }

        Ok(())
    }
}

impl std::fmt::Debug for Lien {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Lien::Our => write!(f, "our"),
            Lien::Shared(place) => write!(f, "shared{{{place:?}}}"),
            Lien::Leased(place) => write!(f, "leased[{place:?}]"),
            Lien::Var(var) => write!(f, "{:?}", var),
        }
    }
}

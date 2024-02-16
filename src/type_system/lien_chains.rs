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
    NamedTy(LienChain, NamedTy),
}

cast_impl!(TyChain);

/// A *lien chain* indicates the "history" of the liens on a given object.
/// For example `shared{x} leased{y}` means that the object was leased from `y`
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

#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Debug, Hash)]
pub struct My();

#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Debug, Hash)]
pub struct Our();

#[derive(Clone, PartialOrd, Ord, PartialEq, Eq, Debug, Hash)]
pub enum LiensLayout {
    ByValue,
    ByRef,
    ByVar(UniversalVar),
}

impl TyChain {
    pub fn lien_chain(&self) -> &LienChain {
        match self {
            TyChain::Var(lien_chain, _) => lien_chain,
            TyChain::NamedTy(lien_chain, _) => lien_chain,
        }
    }
}

impl LienChain {
    fn apply_all(&self, liens: LienChain) -> Self {
        let mut this = self.clone();
        for lien in liens.vec {
            this = this.apply(lien);
        }
        this
    }

    fn apply(&self, lien: Lien) -> Self {
        match (self.vec.last(), &lien) {
            (_, Lien::Our) => LienChain {
                vec: vec![Lien::Our],
            },
            (Some(Lien::Leased(_)), Lien::Shared(_)) | (Some(Lien::Var(_)), Lien::Shared(_)) => {
                LienChain { vec: vec![lien] }
            }
            (None, _)
            | (Some(Lien::Our), _)
            | (Some(Lien::Shared(_)), _)
            | (Some(Lien::Leased(_)), _)
            | (Some(Lien::Var(_)), _) => LienChain {
                vec: self.vec.iter().cloned().chain(Some(lien)).collect(),
            },
        }
    }

    fn apply_lien(&self, lien: Lien, pending: &LienChain) -> (Self, LienChain) {
        let mut this = self.clone();
        let mut pending = pending.vec.iter();

        while let Some(p) = pending.next() {
            if *p == lien {
                // FIXME: should be "p covers lien" (or the reverse?) something.
                break;
            }
            this = this.apply(p.clone());
        }

        (
            this.apply(lien),
            LienChain {
                vec: pending.cloned().collect(),
            },
        )
    }

    fn apply_var(&self, var: impl Upcast<UniversalVar>, pending: &LienChain) -> (Self, LienChain) {
        self.apply_lien(Lien::Var(var.upcast()), pending)
    }

    fn apply_leased(&self, place: impl Upcast<Place>, pending: &LienChain) -> (Self, LienChain) {
        self.apply_lien(Lien::Leased(place.upcast()), pending)
    }

    pub fn layout(&self) -> LiensLayout {
        match self.vec.first() {
            Some(lien) => match lien {
                Lien::Our => {
                    assert!(self.vec.len() == 1);
                    LiensLayout::ByValue
                }
                Lien::Shared(_) => LiensLayout::ByValue,
                Lien::Leased(_) => LiensLayout::ByRef,
                Lien::Var(v) => LiensLayout::ByVar(v.clone()),
            },
            None => LiensLayout::ByValue,
        }
    }
}

impl Lien {
    pub fn shared(place: impl Upcast<Place>) -> Self {
        Self::Shared(place.upcast())
    }

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

pub fn collapse(pairs: Set<(LienChain, LienChain)>) -> Set<LienChain> {
    pairs.into_iter().map(|(a, b)| a.apply_all(b)).collect()
}

judgment_fn! {
    pub fn ty_chains(
        env: Env,
        liens: LienChain,
        a: Ty,
    ) => Set<TyChain> {
        debug(liens, a, env)

        (
            (ty_chains_cx(&env, liens, My(), a) => ty_liens)
            ----------------------------------- ("restrictions")
            (ty_chains(env, liens, a) => ty_liens)
        )
    }
}

judgment_fn! {
    fn ty_chains_cx(
        env: Env,
        chain: LienChain,
        pending: LienChain,
        a: Ty,
    ) => Set<TyChain> {
        debug(chain, pending, a, env)

        (
            (let chain = chain.apply_all(pending))
            ----------------------------------- ("named-ty")
            (ty_chains_cx(_env, chain, pending, n: NamedTy) => set![TyChain::NamedTy(chain, n)])
        )

        (
            (let chain = chain.apply_all(pending))
            ----------------------------------- ("universal-var")
            (ty_chains_cx(_env, chain, pending, v: UniversalVar) => set![TyChain::Var(chain, v)])
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
        liens: LienChain,
        a: Parameter,
    ) => Set<LienChain> {
        debug(liens, a, env)

        (
            (lien_chain_pairs(&env, liens, My(), a) => pairs)
            ----------------------------------- ("restrictions")
            (lien_chains(env, liens, a) => collapse(pairs))
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
            (let pair = chain.apply_var(var, &pending))
            ----------------------------------- ("perm-var")
            (lien_chain_pairs(_env, chain, pending, Variable::UniversalVar(var)) => set![pair])
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
    chain: impl Upcast<LienChain>,
    pending: impl Upcast<Set<(LienChain, LienChain)>>,
) -> Set<(LienChain, LienChain)> {
    let chain = chain.upcast();
    let pending = pending.upcast();
    pending
        .into_iter()
        .map(|(a, b)| (chain.clone(), a.apply_all(b)))
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
            (given_from_places(env, chain, pending, Cons(place, places)) => (collapse_to_pending(&chain, &pairs0), pairs1))
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
            (let (liens_l, pending_l) = chain.apply_leased(&place, &pending))
            (lien_chain_pairs(&env, My(), &pending_l, ty) => pairs0)
            (leased_from_places(&env, &chain, &pending, &places) => pairs1)
            -------------------------- ("cons")
            (leased_from_places(env, chain, pending, Cons(place, places)) => (collapse_to_pending(&liens_l, &pairs0), pairs1))
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
            (shared_from_places(env, Cons(place, places)) => (collapse_to_pending(Lien::shared(&place), &pairs0), pairs1))
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
            Lien::Leased(place) => write!(f, "leased{{{place:?}}}"),
            Lien::Var(var) => write!(f, "{:?}", var),
        }
    }
}

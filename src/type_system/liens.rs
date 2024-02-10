use formality_core::{
    cast_impl, judgment_fn, set, Cons, Downcast, DowncastTo, Set, SetExt, Upcast, UpcastFrom,
};

use crate::{
    dada_lang::grammar::{UniversalVar, Variable},
    grammar::{Kind, NamedTy, Parameter, Perm, Place, Ty},
    type_system::{env::Env, places::place_ty},
};

#[derive(Clone, PartialOrd, Ord, PartialEq, Eq, Debug, Hash)]
pub enum TyLiens {
    Var(Liens, UniversalVar),
    NamedTy(Liens, NamedTy),
}

cast_impl!(TyLiens);

#[derive(Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct Liens {
    pub vec: Vec<Lien>,
}

cast_impl!(Liens);

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

impl Liens {
    fn apply_all(&self, liens: Liens) -> Self {
        let mut this = self.clone();
        for lien in liens.vec {
            this = this.apply(lien);
        }
        this
    }

    fn apply(&self, lien: Lien) -> Self {
        match (self.vec.last(), &lien) {
            (Some(Lien::Our), _) | (_, Lien::Our) => Liens {
                vec: vec![Lien::Our],
            },
            (Some(Lien::Leased(_)), Lien::Shared(_)) | (Some(Lien::Var(_)), Lien::Shared(_)) => {
                Liens { vec: vec![lien] }
            }
            (None, _)
            | (Some(Lien::Shared(_)), _)
            | (Some(Lien::Leased(_)), _)
            | (Some(Lien::Var(_)), _) => Liens {
                vec: self.vec.iter().cloned().chain(Some(lien)).collect(),
            },
        }
    }

    fn apply_lien(&self, lien: Lien, pending: &Liens) -> (Self, Liens) {
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
            Liens {
                vec: pending.cloned().collect(),
            },
        )
    }

    fn apply_var(&self, var: impl Upcast<UniversalVar>, pending: &Liens) -> (Self, Liens) {
        self.apply_lien(Lien::Var(var.upcast()), pending)
    }

    fn apply_leased(&self, place: impl Upcast<Place>, pending: &Liens) -> (Self, Liens) {
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
    fn shared(place: impl Upcast<Place>) -> Self {
        Self::Shared(place.upcast())
    }

    fn leased(place: impl Upcast<Place>) -> Self {
        Self::Leased(place.upcast())
    }
}

impl UpcastFrom<My> for Liens {
    fn upcast_from(_: My) -> Self {
        Self { vec: vec![] }
    }
}

impl UpcastFrom<Our> for Liens {
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

impl UpcastFrom<Lien> for Liens {
    fn upcast_from(lien: Lien) -> Self {
        Self { vec: vec![lien] }
    }
}

impl UpcastFrom<Our> for Lien {
    fn upcast_from(_: Our) -> Self {
        Lien::Our
    }
}

impl DowncastTo<My> for Liens {
    fn downcast_to(&self) -> Option<My> {
        if self.vec.is_empty() {
            Some(My())
        } else {
            None
        }
    }
}

impl DowncastTo<Our> for Liens {
    fn downcast_to(&self) -> Option<Our> {
        if self.vec.len() == 1 && matches!(self.vec[0], Lien::Our) {
            Some(Our())
        } else {
            None
        }
    }
}

impl DowncastTo<Cons<Lien, Liens>> for Liens {
    fn downcast_to(&self) -> Option<Cons<Lien, Liens>> {
        let Cons(lien, liens) = self.vec.downcast()?;
        Some(Cons(lien, Liens { vec: liens }))
    }
}

pub fn collapse(pairs: Set<(Liens, Liens)>) -> Set<Liens> {
    pairs.into_iter().map(|(a, b)| a.apply_all(b)).collect()
}

judgment_fn! {
    pub fn ty_liens(
        env: Env,
        liens: Liens,
        a: Ty,
    ) => (Env, Set<TyLiens>) {
        debug(liens, a, env)

        (
            (ty_liens_in(env, liens, My(), a) => (env, ty_liens))
            ----------------------------------- ("restrictions")
            (ty_liens(env, liens, a) => (env, ty_liens))
        )
    }
}

judgment_fn! {
    fn ty_liens_in(
        env: Env,
        liens: Liens,
        pending: Liens,
        a: Ty,
    ) => (Env, Set<TyLiens>) {
        debug(liens, pending, a, env)

        (
            (let liens = liens.apply_all(pending))
            ----------------------------------- ("named-ty")
            (ty_liens_in(env, liens, pending, n: NamedTy) => (env, set![TyLiens::NamedTy(liens, n)]))
        )

        (
            (let liens = liens.apply_all(pending))
            ----------------------------------- ("universal-var")
            (ty_liens_in(env, liens, pending, v: UniversalVar) => (env, set![TyLiens::Var(liens, v)]))
        )

        (
            (lien_pairs(env, liens, pending, perm) => (env, pairs))
            (ty_apply(env, pairs, &*ty) => (env, ty_skels))
            ----------------------------------- ("apply")
            (ty_liens_in(env, liens, pending, Ty::ApplyPerm(perm, ty)) => (env, ty_skels))
        )

        (
            (ty_liens_in(env, &liens, &pending, &*ty0) => (env, ty_liens0))
            (ty_liens_in(env, &liens, &pending, &*ty1) => (env, ty_liens1))
            ----------------------------------- ("or")
            (ty_liens_in(env, liens, pending, Ty::Or(ty0, ty1)) => (env, (&ty_liens0).union_with(ty_liens1)))
        )
    }
}

judgment_fn! {
    fn ty_apply(
        env: Env,
        pairs: Set<(Liens, Liens)>,
        ty: Ty,
    ) => (Env, Set<TyLiens>) {
        debug(pairs, ty, env)

        (
            -------------------------- ("nil")
            (ty_apply(env, (), _ty) => (env, ()))
        )

        (
            (ty_liens_in(&env, liens, pending, &ty) => (env, ty_liens0))
            (ty_apply(env, &pairs, &ty) => (env, ty_liens1))
            -------------------------- ("cons")
            (ty_apply(env, Cons((liens, pending), pairs), ty) => (env, (&ty_liens0).union_with(ty_liens1)))
        )
    }
}

judgment_fn! {
    pub fn liens(
        env: Env,
        liens: Liens,
        a: Parameter,
    ) => (Env, Set<Liens>) {
        debug(liens, a, env)

        (
            (lien_pairs(env, liens, My(), a) => (env, pairs))
            ----------------------------------- ("restrictions")
            (liens(env, liens, a) => (env, collapse(pairs)))
        )
    }
}

judgment_fn! {
    fn lien_pairs(
        env: Env,
        liens: Liens,
        pending: Liens,
        a: Parameter,
    ) => (Env, Set<(Liens, Liens)>) {
        debug(liens, pending, a, env)

        (
            ----------------------------------- ("my")
            (lien_pairs(env, liens, pending, Perm::My) => (env, set![(liens, pending)]))
        )

        (
            ----------------------------------- ("our")
            (lien_pairs(env, _liens, _pending, Perm::Our) => (env, set![(Our(), My())]))
        )

        (
            (given_from_places(env, liens, pending, places) => (env, pairs))
            ----------------------------------- ("given")
            (lien_pairs(env, liens, pending, Perm::Given(places)) => (env, pairs))
        )

        (
            (shared_from_places(env, places) => (env, pairs))
            ----------------------------------- ("shared")
            (lien_pairs(env, _liens, _pending, Perm::Shared(places)) => (env, pairs))
        )

        (
            (leased_from_places(env, liens, pending, places) => (env, pairs))
            ----------------------------------- ("leased")
            (lien_pairs(env, liens, pending, Perm::Leased(places)) => (env, pairs))
        )

        (
            (if var.kind == Kind::Perm)!
            (let pair = liens.apply_var(var, &pending))
            ----------------------------------- ("perm-var")
            (lien_pairs(env, liens, pending, Variable::UniversalVar(var)) => (env, set![pair]))
        )

        (
            (if var.kind == Kind::Ty)!
            ----------------------------------- ("ty-var")
            (lien_pairs(env, skel, pending, Variable::UniversalVar(var)) => (env, set![(skel, pending)]))
        )

        (
            (lien_pairs(env, skel, pending, &*perm0) => (env, pairs))
            (apply(env, pairs, &*perm1) => (env, pairs))
            ----------------------------------- ("perm-apply")
            (lien_pairs(env, skel, pending, Perm::Apply(perm0, perm1)) => (env, pairs))
        )

        (
            (lien_pairs(env, skel, pending, perm) => (env, pairs))
            (apply(env, pairs, &*ty) => (env, pairs))
            ----------------------------------- ("ty-apply")
            (lien_pairs(env, skel, pending, Ty::ApplyPerm(perm, ty)) => (env, pairs))
        )

        (
            (lien_pairs(env, &skel, &pending, &*perm0) => (env, pairs0))
            (lien_pairs(env, &skel, &pending, &*perm1) => (env, pairs1))
            ----------------------------------- ("perm-or")
            (lien_pairs(env, skel, pending, Perm::Or(perm0, perm1)) => (env, (&pairs0).union_with(pairs1)))
        )

        (
            (lien_pairs(env, &skel, &pending, &*ty0) => (env, pairs0))
            (lien_pairs(env, &skel, &pending, &*ty1) => (env, pairs1))
            ----------------------------------- ("ty-or")
            (lien_pairs(env, skel, pending, Ty::Or(ty0, ty1)) => (env, (&pairs0).union_with(pairs1)))
        )

        (
            ----------------------------------- ("named-ty")
            (lien_pairs(env, skel, pending, NamedTy { .. }) => (env, set![(skel, pending)]))
        )
    }
}

judgment_fn! {
    pub fn flat_liens(
        env: Env,
        a: Liens,
    ) => (Env, Set<Lien>) {
        debug(a, env)

        (
            ----------------------------------- ("my")
            (flat_liens(env, My()) => (env, ()))
        )

        (
            (assert liens.vec.is_empty())
            ----------------------------------- ("our")
            (flat_liens(env, Cons(Lien::Our, liens)) => (env, set![Lien::Our]))
        )

        (
            (let shared_lien = set![Lien::shared(&place)])
            (flat_liens_from_place(env, place) => (env, lien_set0))
            (flat_liens(env, &liens) => (env, lien_set1))
            ----------------------------------- ("sh")
            (flat_liens(env, Cons(Lien::Shared(place), liens)) => (env, (&shared_lien, &lien_set0, lien_set1)))
        )

        (
            (let leased_lien = set![Lien::leased(&place)])
            (flat_liens_from_place(env, place) => (env, lien_set0))
            (flat_liens(env, &liens) => (env, lien_set1))
            ----------------------------------- ("l")
            (flat_liens(env, Cons(Lien::Leased(place), liens)) => (env, (&leased_lien, &lien_set0, lien_set1)))
        )


        (
            (let var_lien = set![Lien::Var(var)])
            (flat_liens(env, liens) => (env, lien_set1))
            ----------------------------------- ("var")
            (flat_liens(env, Cons(Lien::Var(var), liens)) => (env, (&var_lien, lien_set1)))
        )
    }
}

judgment_fn! {
    fn flat_liens_from_place(
        env: Env,
        a: Place,
    ) => (Env, Set<Lien>) {
        debug(a, env)

        (
            (place_ty(&env, &place) => ty)
            (flat_liens_from_parameter(&env, ty) => (env, lien_set))
            ----------------------------------- ("nil")
            (flat_liens_from_place(env, place) => (env, lien_set))
        )

    }
}

judgment_fn! {
    fn flat_liens_from_parameter(
        env: Env,
        a: Parameter,
    ) => (Env, Set<Lien>) {
        debug(a, env)

        (
            (ty_liens(env, My(), ty) => (env, ty_liens_set))
            (flatten_ty_liens_set(env, ty_liens_set) => (env, lien_set))
            ----------------------------------- ("nil")
            (flat_liens_from_parameter(env, ty: Ty) => (env, lien_set))
        )

        (
            (liens(env, My(), perm) => (env, liens_set))
            (flatten_liens_set(env, liens_set) => (env, lien_set))
            ----------------------------------- ("nil")
            (flat_liens_from_parameter(env, perm: Perm) => (env, lien_set))
        )
    }
}

judgment_fn! {
    fn flat_liens_from_parameters(
        env: Env,
        a: Vec<Parameter>,
    ) => (Env, Set<Lien>) {
        debug(a, env)

        (
            ----------------------------------- ("nil")
            (flat_liens_from_parameters(env, ()) => (env, ()))
        )


        (
            (flat_liens_from_parameter(env, p) => (env, lien_set0))
            (flat_liens_from_parameters(env, &ps) => (env, lien_set1))
            ----------------------------------- ("cons")
            (flat_liens_from_parameters(env, Cons(p, ps)) => (env, (&lien_set0, lien_set1)))
        )
    }
}

judgment_fn! {
    fn flatten_ty_liens_set(
        env: Env,
        a: Set<TyLiens>,
    ) => (Env, Set<Lien>) {
        debug(a, env)

        (
            ----------------------------------- ("nil")
            (flatten_ty_liens_set(env, ()) => (env, ()))
        )

        (
            (flat_liens(env, liens) => (env, lien_set0))
            (flatten_ty_liens_set(env, &liens1) => (env, lien_set1))
            ----------------------------------- ("nil")
            (flatten_ty_liens_set(env, Cons(TyLiens::Var(liens, _), liens1)) => (env, (&lien_set0, lien_set1)))
        )

        (
            (flat_liens(env, liens) => (env, lien_set0))
            (flatten_ty_liens_set(env, &liens1) => (env, lien_set1))
            (flat_liens_from_parameters(env, &parameters) => (env, lien_set2))
            ----------------------------------- ("nil")
            (flatten_ty_liens_set(env, Cons(TyLiens::NamedTy(liens, NamedTy { name: _, parameters }), liens1)) => (env, (&lien_set0, &lien_set1, lien_set2)))
        )
    }
}

judgment_fn! {
    fn flatten_liens_set(
        env: Env,
        a: Set<Liens>,
    ) => (Env, Set<Lien>) {
        debug(a, env)

        (
            ----------------------------------- ("nil")
            (flatten_liens_set(env, ()) => (env, ()))
        )

        (
            (flat_liens(env, liens0) => (env, lien_set0))
            (flatten_liens_set(env, &liens1) => (env, lien_set1))
            ----------------------------------- ("nil")
            (flatten_liens_set(env, Cons(liens0, liens1)) => (env, (&lien_set0, lien_set1)))
        )
    }
}

fn collapse_to_pending(
    liens: impl Upcast<Liens>,
    pending: impl Upcast<Set<(Liens, Liens)>>,
) -> Set<(Liens, Liens)> {
    let liens = liens.upcast();
    let pending = pending.upcast();
    pending
        .into_iter()
        .map(|(a, b)| (liens.clone(), a.apply_all(b)))
        .collect()
}

judgment_fn! {
    fn given_from_places(
        env: Env,
        liens: Liens,
        pending: Liens,
        places: Set<Place>,
    ) => (Env, Set<(Liens, Liens)>) {
        debug(liens, pending, places, env)

        (
            -------------------------- ("nil")
            (given_from_places(env, _lines, _pending, ()) => (env, ()))
        )

        (
            (place_ty(&env, &place) => ty)
            (lien_pairs(&env, My(), &pending, ty) => (env, pairs0))
            (given_from_places(env, &liens, &pending, &places) => (env, pairs1))
            -------------------------- ("cons")
            (given_from_places(env, liens, pending, Cons(place, places)) => (env, (collapse_to_pending(&liens, &pairs0), pairs1)))
        )
    }
}

judgment_fn! {
    fn leased_from_places(
        env: Env,
        liens: Liens,
        pending: Liens,
        places: Set<Place>,
    ) => (Env, Set<(Liens, Liens)>) {
        debug(liens, pending, places, env)

        (
            -------------------------- ("nil")
            (leased_from_places(env, _lines, _pending, ()) => (env, ()))
        )

        (
            (place_ty(&env, &place) => ty)
            (let (liens_l, pending_l) = liens.apply_leased(&place, &pending))
            (lien_pairs(&env, My(), &pending_l, ty) => (env, pairs0))
            (leased_from_places(env, &liens, &pending, &places) => (env, pairs1))
            -------------------------- ("cons")
            (leased_from_places(env, liens, pending, Cons(place, places)) => (env, (collapse_to_pending(&liens_l, &pairs0), pairs1)))
        )
    }
}
judgment_fn! {
    fn shared_from_places(
        env: Env,
        places: Set<Place>,
    ) => (Env, Set<(Liens, Liens)>) {
        debug(places, env)

        (
            -------------------------- ("nil")
            (shared_from_places(env, ()) => (env, ()))
        )

        (
            (place_ty(&env, &place) => ty)
            (lien_pairs(&env, My(), My(), ty) => (env, pairs0))
            (shared_from_places(env, &places) => (env, pairs1))
            -------------------------- ("cons")
            (shared_from_places(env, Cons(place, places)) => (env, (collapse_to_pending(Lien::shared(&place), &pairs0), pairs1)))
        )
    }
}

judgment_fn! {
    fn apply(
        env: Env,
        pairs: Set<(Liens, Liens)>,
        parameter: Parameter,
    ) => (Env, Set<(Liens, Liens)>) {
        debug(pairs, parameter, env)

        (
            -------------------------- ("nil")
            (apply(env, (), _parameter) => (env, ()))
        )

        (
            (lien_pairs(&env, liens, pending, &parameter) => (env, pairs0))
            (apply(env, &pairs, &parameter) => (env, pairs1))
            -------------------------- ("cons")
            (apply(env, Cons((liens, pending), pairs), parameter) => (env, (&pairs0, pairs1)))
        )
    }
}

impl std::fmt::Debug for Liens {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.vec.len() == 0 {
            return write!(f, "my");
        }

        let mut prefix = "";
        for lien in &self.vec {
            write!(f, "{}{:?}", prefix, lien)?;
            prefix = ", ";
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

use super::{Parameter, Perm, Ty};
use formality_core::{cast_impl, Cons, DowncastFrom, Upcast, UpcastFrom};
use std::sync::Arc;

impl Perm {
    pub fn apply_to_parameter(&self, p: &Parameter) -> Parameter {
        match p {
            Parameter::Ty(ty) => Ty::apply_perm(self, ty).upcast(),
            Parameter::Perm(perm) => Perm::apply(self, perm).upcast(),
        }
    }

    /// Returns a new permission that is the conjunction of this permission and the given
    /// permission.
    pub fn apply_to(&self, perm: impl Upcast<Arc<Perm>>) -> Perm {
        Perm::apply(self, perm)
    }
}

/// "LeafPerms"
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct LeafPerms {
    leaves: Vec<Perm>,
}

cast_impl!(LeafPerms);
cast_impl!((LeafPerms) <: (Perm) <: (Parameter));

impl IntoIterator for LeafPerms {
    type Item = Perm;
    type IntoIter = std::vec::IntoIter<Perm>;

    fn into_iter(self) -> Self::IntoIter {
        self.leaves.into_iter()
    }
}

impl Perm {
    /// Create a Perm from an iterator of leaves.
    /// It has the shape `Apply(leaf, Apply(leaf, ...))`
    fn from_leaves(leaves: impl DoubleEndedIterator<Item = Perm>) -> Self {
        let mut leaves = leaves.into_iter().rev();
        let Some(leaf_n) = leaves.next() else {
            return Perm::Given;
        };
        leaves.fold(leaf_n.upcast(), |n_1, n_0| Perm::apply(n_0, n_1))
    }

    fn push_leaves(&self, output: &mut Vec<Perm>) {
        match self {
            Perm::Given => (),
            Perm::Shared | Perm::Mv(_) | Perm::Rf(_) | Perm::Mt(_) | Perm::Var(_) => {
                output.push(self.clone())
            }
            Perm::Apply(perm, perm1) => {
                perm.push_leaves(output);
                perm1.push_leaves(output);
            }
        }
    }
}

impl UpcastFrom<Perm> for LeafPerms {
    fn upcast_from(t: Perm) -> Self {
        let mut leaves = vec![];
        t.push_leaves(&mut leaves);
        LeafPerms { leaves }
    }
}

impl DowncastFrom<Perm> for LeafPerms {
    fn downcast_from(p: &Perm) -> Option<Self> {
        Some(p.upcast())
    }
}

impl UpcastFrom<LeafPerms> for Perm {
    fn upcast_from(t: LeafPerms) -> Self {
        Perm::from_leaves(t.leaves.into_iter())
    }
}

impl DowncastFrom<LeafPerms> for Perm {
    fn downcast_from(p: &LeafPerms) -> Option<Self> {
        Some(Perm::from_leaves(p.leaves.iter().cloned()))
    }
}

impl<C: PermCar> DowncastFrom<LeafPerms> for Cons<C, Perm> {
    fn downcast_from(perm: &LeafPerms) -> Option<Self> {
        let mut leaves = perm.leaves.iter().cloned();
        let array = C::take(&mut leaves)?;
        Some(Cons(array, Perm::from_leaves(leaves)))
    }
}

impl<C: PermCar, D: Upcast<LeafPerms>> UpcastFrom<Cons<C, D>> for LeafPerms {
    fn upcast_from(term: Cons<C, D>) -> Self {
        let Cons(car, cdr) = term;
        let cdr: LeafPerms = cdr.upcast();
        let mut leaves = vec![];
        leaves.extend(car.into_perms());
        leaves.extend(cdr.leaves);
        LeafPerms { leaves }
    }
}

trait PermCar: Sized + Clone {
    fn take(leaves: &mut impl Iterator<Item = Perm>) -> Option<Self>;
    fn into_perms(self) -> impl IntoIterator<Item = Perm>;
}

impl PermCar for Perm {
    fn take(leaves: &mut impl Iterator<Item = Perm>) -> Option<Self> {
        leaves.next()
    }

    fn into_perms(self) -> impl IntoIterator<Item = Perm> {
        Some(self)
    }
}

impl PermCar for (Perm, Perm) {
    fn take(leaves: &mut impl Iterator<Item = Perm>) -> Option<Self> {
        let car = leaves.next()?;
        let cdr = leaves.next()?;
        Some((car, cdr))
    }

    fn into_perms(self) -> impl IntoIterator<Item = Perm> {
        [self.0, self.1]
    }
}

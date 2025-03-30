use formality_core::{cast_impl, Cons, DowncastFrom, Upcast, UpcastFrom};

use super::{Parameter, Perm, Ty};

impl Perm {
    pub fn apply_to(&self, p: &Parameter) -> Parameter {
        match p {
            Parameter::Ty(ty) => Ty::apply_perm(self, ty).upcast(),
            Parameter::Perm(perm) => Perm::apply(self, perm).upcast(),
        }
    }
}

/// "LeafPerms"
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
pub struct LeafPerms {
    leaves: Vec<Perm>,
}

cast_impl!(LeafPerms);

impl IntoIterator for LeafPerms {
    type Item = Perm;
    type IntoIter = std::vec::IntoIter<Perm>;

    fn into_iter(self) -> Self::IntoIter {
        self.leaves.into_iter()
    }
}

impl Perm {
    /// Create a Perm from an iterator of leaves.
    fn from_leaves(leaves: impl IntoIterator<Item = Perm>) -> Self {
        let mut leaves = leaves.into_iter();
        let Some(leaf0) = leaves.next() else {
            return Perm::My;
        };
        leaves.fold(leaf0.upcast(), |l, r| Perm::apply(l, r))
    }

    fn push_leaves(&self, output: &mut Vec<Perm>) {
        match self {
            Perm::My => (),
            Perm::Our | Perm::Given(_) | Perm::Shared(_) | Perm::Leased(_) | Perm::Var(_) => {
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

impl UpcastFrom<LeafPerms> for Perm {
    fn upcast_from(t: LeafPerms) -> Self {
        Perm::from_leaves(t.leaves)
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

trait PermCar: Sized {
    fn take(leaves: &mut impl Iterator<Item = Perm>) -> Option<Self>;
}

impl PermCar for Perm {
    fn take(leaves: &mut impl Iterator<Item = Perm>) -> Option<Self> {
        leaves.next()
    }
}

impl PermCar for (Perm, Perm) {
    fn take(leaves: &mut impl Iterator<Item = Perm>) -> Option<Self> {
        let car = leaves.next()?;
        let cdr = leaves.next()?;
        Some((car, cdr))
    }
}

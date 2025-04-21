use std::sync::Arc;

use formality_core::{cast_impl, term, Downcast, DowncastFrom, Set, Upcast, UpcastFrom};

use crate::grammar::{Parameter, Perm, Place, Variable};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Leaf {
    Place(Access, Place),
    Places(Access, Set<Place>),
    My,
    Our,
    Var(Variable),
}

cast_impl!(Leaf);

#[term]
#[derive(Copy)]
pub enum Access {
    Mt,
    Mv,
    Rf,
}

impl Leaf {
    pub fn place(acc: impl Upcast<Access>, place: impl Upcast<Place>) -> Leaf {
        Leaf::Place(acc.upcast(), place.upcast())
    }

    fn place_or_places(kind: Access, set: &Set<Place>) -> Leaf {
        let set: Set<Place> = set.upcast();
        if set.len() == 1 {
            Leaf::Place(kind, set.first().unwrap().clone())
        } else {
            Leaf::Places(kind, set.clone())
        }
    }

    fn access_to_perm(kind: Access, set: impl Upcast<Set<Place>>) -> Perm {
        match kind {
            Access::Rf => Perm::rf(set),
            Access::Mv => Perm::mv(set),
            Access::Mt => Perm::mt(set),
        }
    }
}

impl DowncastFrom<Perm> for Leaf {
    fn downcast_from(term: &Perm) -> Option<Self> {
        match term {
            Perm::My => Some(Leaf::My),
            Perm::Our => Some(Leaf::Our),
            Perm::Mv(set) => Some(Leaf::place_or_places(Access::Mv, set)),
            Perm::Rf(set) => Some(Leaf::place_or_places(Access::Rf, set)),
            Perm::Mt(set) => Some(Leaf::place_or_places(Access::Mt, set)),
            Perm::Var(v) => Some(Leaf::Var(v.clone())),
            Perm::Apply(..) => None,
        }
    }
}

impl UpcastFrom<Leaf> for Perm {
    fn upcast_from(pm: Leaf) -> Perm {
        match pm {
            Leaf::Place(kind, place) => Leaf::access_to_perm(kind, (place,)),
            Leaf::Places(kind, set) => Leaf::access_to_perm(kind, set),
            Leaf::My => Perm::My,
            Leaf::Our => Perm::Our,
            Leaf::Var(v) => Perm::var(v),
        }
    }
}

impl UpcastFrom<Leaf> for Arc<Perm> {
    fn upcast_from(leaf: Leaf) -> Self {
        Arc::new(leaf.upcast())
    }
}

impl UpcastFrom<Leaf> for Parameter {
    fn upcast_from(term: Leaf) -> Self {
        Parameter::upcast_from(Perm::upcast_from(term))
    }
}

fn flatten_perm(perm: &Perm, output: &mut Vec<Leaf>) {
    if let Perm::Apply(l, r) = perm {
        flatten_perm(l, output);
        flatten_perm(r, output);
    } else {
        output.push(perm.downcast().unwrap());
    }
}

/// Matches a permission into an application.
///
/// This differs from matching on `Perm::Apply` because
/// it applies various equivalences:
///
/// * we leverage fact that permissions are associative
///   to ensure that the `L` is always a "leaf perm"
///   (not itself an `Apply`);
/// * we convert a leaf perm into an application to `My`.
///
/// Use it like `Head(head, Tail(tail))` or `Head(head, Head(head1, Tail(tail))`.
#[derive(Clone, Debug)]
pub struct Head<H, T>(pub H, pub T);

impl<T> DowncastFrom<Perm> for Head<Leaf, T>
where
    T: for<'a> DowncastFrom<&'a [Leaf]>,
{
    fn downcast_from(perm: &Perm) -> Option<Self> {
        let mut heads = vec![];
        flatten_perm(perm, &mut heads);
        Self::downcast_from(&&heads[..])
    }
}

impl<T> DowncastFrom<&[Leaf]> for Head<Leaf, T>
where
    T: for<'a> DowncastFrom<&'a [Leaf]>,
{
    fn downcast_from(v: &&[Leaf]) -> Option<Self> {
        let Some((head, tail)) = v.split_first() else {
            return None;
        };
        Some(Head(head.clone(), tail.downcast()?))
    }
}

impl<H, T> UpcastFrom<Head<H, T>> for Perm
where
    H: Upcast<Perm>,
    T: Upcast<Leaves>,
{
    fn upcast_from(Head(head, tail): Head<H, T>) -> Self {
        let head: Perm = head.upcast();
        let tail: Leaves = tail.upcast();
        match tail.into_tail() {
            Some(tail) => Perm::apply(head, tail),
            None => head,
        }
    }
}
impl<H, T> UpcastFrom<Head<H, T>> for Parameter
where
    H: Upcast<Perm>,
    T: Upcast<Leaves>,
{
    fn upcast_from(value: Head<H, T>) -> Parameter {
        let perm: Perm = value.upcast();
        perm.upcast()
    }
}

#[derive(Clone, Debug)]
pub struct Tail<L>(pub L);

impl DowncastFrom<&[Leaf]> for Tail<Leaves> {
    fn downcast_from(slice: &&[Leaf]) -> Option<Self> {
        Some(Tail(Leaves(slice.iter().cloned().collect())))
    }
}

impl<L> UpcastFrom<Tail<L>> for Leaves
where
    L: Upcast<Leaves>,
{
    fn upcast_from(Tail(leaves): Tail<L>) -> Leaves {
        leaves.upcast()
    }
}

/// A vector of leaves that form the "tail" of a
/// flattened permission. The vector could be empty.
#[derive(Clone, Debug)]
pub struct Leaves(Vec<Leaf>);

cast_impl!(Leaves);

impl Leaves {
    /// Convert the leaf perms into a perm like
    /// `Apply(Leaf0, Apply(Leaf1, Apply(Leaf2, ...)))`
    /// or return None if the list is empty.
    fn into_tail(self) -> Option<Perm> {
        let Leaves(leaves) = self;
        let mut leaves = leaves.into_iter().rev();
        let Some(leaf) = leaves.next() else {
            // No leaves?
            return None;
        };
        let mut tail: Perm = leaf.upcast();
        for leaf in leaves {
            tail = Perm::apply(leaf, tail);
        }
        Some(tail)
    }
}

impl From<Vec<Leaf>> for Leaves {
    fn from(v: Vec<Leaf>) -> Leaves {
        Leaves(v)
    }
}

impl DowncastFrom<Perm> for Leaves {
    fn downcast_from(perm: &Perm) -> Option<Self> {
        Some(perm.clone().upcast())
    }
}

impl UpcastFrom<Perm> for Leaves {
    fn upcast_from(perm: Perm) -> Self {
        let mut heads = vec![];
        flatten_perm(&perm, &mut heads);
        Leaves(heads)
    }
}

impl UpcastFrom<Leaves> for Perm {
    fn upcast_from(leaves: Leaves) -> Self {
        match leaves.into_tail() {
            Some(tail) => tail,
            None => Perm::My,
        }
    }
}

impl UpcastFrom<Leaves> for Arc<Perm> {
    fn upcast_from(perm: Leaves) -> Self {
        Arc::new(perm.upcast())
    }
}

impl UpcastFrom<Leaves> for Parameter {
    fn upcast_from(term: Leaves) -> Self {
        Parameter::upcast_from(Perm::upcast_from(term))
    }
}

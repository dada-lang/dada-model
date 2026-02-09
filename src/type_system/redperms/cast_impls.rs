use formality_core::{cast_impl, Downcast, DowncastFrom, Upcast, UpcastFrom};

use crate::grammar::{Parameter, Perm};

use super::{Given, Head, RedChain, RedLink, Tail};

cast_impl!(RedLink);

impl UpcastFrom<RedLink> for RedChain {
    fn upcast_from(term: RedLink) -> Self {
        RedChain { links: vec![term] }
    }
}

impl DowncastFrom<&[RedLink]> for RedChain {
    fn downcast_from(t: &&[RedLink]) -> Option<Self> {
        Some(RedChain { links: t.to_vec() })
    }
}

impl RedChain {
    pub fn given() -> Self {
        RedChain { links: vec![] }
    }
}

impl UpcastFrom<RedChain> for Parameter {
    fn upcast_from(term: RedChain) -> Self {
        let p: Perm = term.upcast();
        p.upcast()
    }
}

impl UpcastFrom<RedChain> for Perm {
    fn upcast_from(term: RedChain) -> Self {
        let mut links = term.links.into_iter();
        let Some(link0) = links.next() else {
            return Perm::Given;
        };

        let perm0: Perm = link0.upcast();
        links.fold(perm0, |l, r| {
            let r: Perm = r.upcast();
            Perm::apply(l, r)
        })
    }
}

impl UpcastFrom<RedLink> for Parameter {
    fn upcast_from(term: RedLink) -> Self {
        let p: Perm = term.upcast();
        p.upcast()
    }
}

impl UpcastFrom<RedLink> for Perm {
    fn upcast_from(term: RedLink) -> Self {
        match term {
            RedLink::Shared => Perm::Shared,
            RedLink::Rfl(place) | RedLink::Rfd(place) => Perm::rf((place,)),
            RedLink::Mtl(place) | RedLink::Mtd(place) => Perm::mt((place,)),
            RedLink::Mv(place) => Perm::mv((place,)),
            RedLink::Var(v) => Perm::var(v),
        }
    }
}

impl DowncastFrom<RedChain> for RedLink {
    fn downcast_from(t: &RedChain) -> Option<Self> {
        match t.links.len() {
            1 => Some(t.links[0].clone()),
            _ => None,
        }
    }
}

impl DowncastFrom<RedChain> for Head<RedChain, RedLink> {
    fn downcast_from(t: &RedChain) -> Option<Self> {
        let Some((link0, links)) = t.links.split_last() else {
            return None;
        };

        Some(Head(links.downcast()?, link0.clone()))
    }
}

impl<T> DowncastFrom<RedChain> for Head<RedLink, T>
where
    T: for<'a> DowncastFrom<&'a [RedLink]>,
{
    fn downcast_from(t: &RedChain) -> Option<Self> {
        Self::downcast_from(&&t.links[..])
    }
}

impl<T> DowncastFrom<&[RedLink]> for Head<RedLink, T>
where
    T: for<'a> DowncastFrom<&'a [RedLink]>,
{
    fn downcast_from(t: &&[RedLink]) -> Option<Self> {
        let Some((link0, links)) = t.split_first() else {
            return None;
        };

        Some(Head(link0.clone(), links.downcast()?))
    }
}

impl<T> UpcastFrom<Head<RedLink, T>> for RedChain
where
    T: Upcast<RedChain>,
{
    fn upcast_from(Head(head, tail): Head<RedLink, T>) -> Self {
        let mut tail: RedChain = tail.upcast();
        tail.links.insert(0, head);
        tail
    }
}

impl UpcastFrom<Given> for RedChain {
    fn upcast_from(_term: Given) -> Self {
        RedChain { links: vec![] }
    }
}

impl DowncastFrom<RedChain> for Given {
    fn downcast_from(t: &RedChain) -> Option<Self> {
        (&t.links[..]).downcast()
    }
}

impl DowncastFrom<&[RedLink]> for Given {
    fn downcast_from(t: &&[RedLink]) -> Option<Self> {
        if t.len() == 0 {
            Some(Given())
        } else {
            None
        }
    }
}

impl DowncastFrom<&[RedLink]> for Tail<RedChain> {
    fn downcast_from(t: &&[RedLink]) -> Option<Self> {
        Some(Tail(RedChain {
            links: t.iter().cloned().collect(),
        }))
    }
}

impl<T> UpcastFrom<Tail<T>> for RedChain
where
    T: Upcast<RedChain>,
{
    fn upcast_from(Tail(tail): Tail<T>) -> RedChain {
        tail.upcast()
    }
}

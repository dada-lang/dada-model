use formality_core::{cast_impl, Cons, Downcast, DowncastFrom, Upcast, UpcastFrom};

use crate::grammar::{Parameter, Perm};

use super::{My, RedChain, RedLink, Tail};

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
    pub fn my() -> Self {
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
            return Perm::My;
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
            RedLink::Our => Perm::Our,
            RedLink::Rf(place) => Perm::rf((place,)),
            RedLink::Mt(place) | RedLink::Mtd(place) => Perm::mt((place,)),
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

impl DowncastFrom<RedChain> for Cons<RedChain, RedLink> {
    fn downcast_from(t: &RedChain) -> Option<Self> {
        let Some((link0, links)) = t.links.split_last() else {
            return None;
        };

        Some(Cons(links.downcast()?, link0.clone()))
    }
}

impl<T> DowncastFrom<RedChain> for Cons<RedLink, T>
where
    T: for<'a> DowncastFrom<&'a [RedLink]>,
{
    fn downcast_from(t: &RedChain) -> Option<Self> {
        let Some((link0, links)) = t.links.split_first() else {
            return None;
        };

        Some(Cons(link0.clone(), links.downcast()?))
    }
}

impl<T> UpcastFrom<Cons<RedLink, T>> for RedChain
where
    T: Upcast<RedChain>,
{
    fn upcast_from(Cons(head, tail): Cons<RedLink, T>) -> Self {
        let mut tail: RedChain = tail.upcast();
        tail.links.insert(0, head);
        tail
    }
}

impl UpcastFrom<My> for RedChain {
    fn upcast_from(_term: My) -> Self {
        RedChain { links: vec![] }
    }
}

impl DowncastFrom<RedChain> for My {
    fn downcast_from(t: &RedChain) -> Option<Self> {
        (&t.links[..]).downcast()
    }
}

impl DowncastFrom<&[RedLink]> for My {
    fn downcast_from(t: &&[RedLink]) -> Option<Self> {
        if t.len() == 0 {
            Some(My())
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

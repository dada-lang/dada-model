use std::sync::Arc;

use formality_core::Upcast;

use crate::grammar::{Perm, Place, Ty};

impl Ty {
    pub fn is_simplified(&self) -> bool {
        *self == self.simplify()
    }

    pub fn simplify(&self) -> Self {
        todo!()
    }
}

impl Perm {
    pub fn is_simplified(&self) -> bool {
        *self == self.simplify()
    }

    pub fn simplify(&self) -> Self {
        match self {
            Perm::My | Perm::Var(_) => self.clone(),
            Perm::Shared(places, perm) => perm.share(places),
            Perm::Leased(places, perm) => perm.lease(places),
        }
    }

    pub fn share(&self, places: impl Upcast<Vec<Place>>) -> Self {
        match self {
            Perm::My | Perm::Var(_) => Self::shared(places, Arc::new(self.clone())),
            Perm::Shared(places1, perm1) => perm1.share(places1),

            // Is this right? See below. This would be like `x.field.share` --
            // if we convert to `shared(x.field) String`, that's not *wrong*, but it's
            // not truly simplified, since in principle we should be able to promote
            // it to `shared(leased y)` or something like that. We could however keep
            // the `leased`, so we get `shared(x.field) leased(y) String`.
            // This is somewhat appealing, though it has some interesting implications
            // I don't fully understand.
            Perm::Leased(_, perm1) => perm1.share(places),
        }
    }

    pub fn lease(&self, places: impl Upcast<Vec<Place>>) -> Self {
        match self {
            Perm::My | Perm::Var(_) => Self::leased(places, Arc::new(self.clone())),
            Perm::Shared(places1, perm1) => perm1.share(places1),

            // This doesn't feel entirely right.
            //
            // Consider if you have a `x: my Box<leased(y) String>`
            // and you do `let p = x.field.lease`. Now `p: leased(x.field) leased(y) String`.
            // But if `x` is dropped, `p` could still be valid and just considered as
            // `leased(y)`. We've lost that information.
            // But merging to `leased(x.field, y)` is also wrong, because that would be
            // invalidated by dropping `x`.
            //
            // In fact `leased(x.field) String` contains all the information needed
            // to recover the original lease, but if it were promoted to `leased(x)`
            // (a valid supertype) then we would not have that information anymore.
            Perm::Leased(_, perm1) => perm1.lease(places),
        }
    }
}

use std::sync::Arc;

use contracts::ensures;
use formality_core::Upcast;

use crate::grammar::{Perm, Ty};

impl Ty {
    pub fn is_simplified(&self) -> bool {
        todo!()
    }

    /// A *simplified* type meets the grammar `Perm? (base type)`.
    /// To create a simplified type, we accumulate the permissions and simplify.
    // #[ensures(ret.is_simplified())]
    pub fn simplify(&self) -> Ty {
        match self {
            Ty::ClassTy(_) | Ty::Var(_) => self.clone(),
            Ty::ApplyPerm(perm0, ty) => {
                let ty = ty.simplify();
                if let Ty::ApplyPerm(perm1, ty1) = ty {
                    let perm2 = perm0.apply_to_perm(perm1);
                    Ty::apply_perm(perm2, ty)
                } else {
                    Ty::apply_perm(perm0, ty)
                }
            }
        }
    }
}

impl Perm {
    pub fn is_simplified(&self) -> bool {
        let mut perm = self;

        // Simplified perms can start with a shared
        if let Self::Shared(_, perm1) = perm {
            perm = perm1;
        }

        // They can then have any number of leases
        while let Self::Leased(_, perm1) = perm {
            perm = perm1;
        }

        // And finally a my|var
        match perm {
            Perm::My | Perm::Var(_) => true,
            _ => false,
        }
    }

    /// A *simplified* permission meets the grammar `shared(_)? leased(_)* var(_)* my`.
    /// To create a simplified perm, we apply the rules that sharing or leasing a shared thing
    /// just results in the original shared thing. Otherwise, we preserve what is there.
    #[ensures(ret.is_simplified())]
    pub fn simplify(&self) -> Perm {
        match self {
            Perm::My | Perm::Var(_) => self.clone(),
            Perm::Shared(places, perm) => {
                let perm = perm.simplify();
                if let Perm::Shared(..) = perm {
                    perm
                } else {
                    Perm::shared(places, perm)
                }
            }
            Perm::Leased(places, perm) => {
                let perm = perm.simplify();
                if let Perm::Shared(..) = perm {
                    perm
                } else {
                    Perm::leased(places, perm)
                }
            }
        }
    }
}

use contracts::ensures;

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
                let perm0 = perm0.simplify();
                let ty = ty.simplify();
                if let Ty::ApplyPerm(perm1, ty1) = ty {
                    let perm2 = perm0.rebase(perm1);
                    Ty::apply_perm(perm2, ty1)
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

        // They can then have any number of leases or variables
        while let Self::Leased(_, perm1) | Self::Var(_, perm1) = perm {
            perm = perm1;
        }

        // And finally an owned
        matches!(perm, Perm::Owned)
    }

    /// A *simplified* permission meets the grammar `shared(_)? leased(_)* var(_)* my`.
    /// To create a simplified perm, we apply the rules that sharing or leasing a shared thing
    /// just results in the original shared thing. Otherwise, we preserve what is there.
    #[ensures(ret.is_simplified())]
    pub fn simplify(&self) -> Perm {
        match self {
            Perm::Owned => Perm::Owned,
            Perm::Var(var, perm) => {
                let perm = perm.simplify();
                if let Perm::Shared(..) = perm {
                    perm
                } else {
                    Perm::var(var, perm)
                }
            }
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

#[test]
fn simplify_perm() {
    use crate::dada_lang::term;
    let p: Perm = term("shared(x) leased(y) owned");
}

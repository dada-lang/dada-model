use formality_core::{cast_impl, DowncastFrom, To, Upcast, UpcastFrom};

use super::{Parameter, Perm, Ty};

/// An alternative syntax for a `Ty` -- all permissions shuffled into the `Perm`
/// and the `Ty` is guaranteed to be a named ty, var, etc.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq, Debug, Hash)]
pub struct PermTy(pub Perm, pub Ty);

cast_impl!(PermTy);
cast_impl!((PermTy) <: (Ty) <: (Parameter));

impl UpcastFrom<Ty> for PermTy {
    fn upcast_from(ty: Ty) -> Self {
        match ty {
            Ty::NamedTy(_) | Ty::Var(_) => PermTy(Perm::Given, ty),

            Ty::ApplyPerm(perm0, ty) => {
                let ty = &*ty;
                let PermTy(perm1, ty1) = ty.to();
                if let Perm::Given = perm1 {
                    // microspecial case
                    PermTy(perm0, ty1)
                } else {
                    PermTy(Perm::apply(perm0, perm1), ty1.upcast())
                }
            }
        }
    }
}

impl DowncastFrom<Ty> for PermTy {
    fn downcast_from(t: &Ty) -> Option<Self> {
        Some(t.upcast())
    }
}

impl UpcastFrom<PermTy> for Ty {
    fn upcast_from(PermTy(perm, ty): PermTy) -> Ty {
        if let Perm::Given = perm {
            ty
        } else {
            Ty::apply_perm(perm, ty)
        }
    }
}

impl DowncastFrom<PermTy> for Ty {
    fn downcast_from(t: &PermTy) -> Option<Self> {
        Some(t.upcast())
    }
}

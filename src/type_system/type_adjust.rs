use crate::grammar::{Perm, Place, Ty};

/// Adjusts a permission: if you accessing a field declared as `inner_perm`
/// with an object reference that has `outer_perm`
pub fn adjust_type(outer_perm: &Perm, inner_ty: &Ty) -> Ty {
    match inner_ty {
        Ty::ClassTy(_) => todo!(),
        Ty::TupleTy(_) => todo!(),
        Ty::Var(_) => todo!(),
    }
}

/// Adjusts a permission: if you accessing a field declared as `inner_perm`
/// with an object reference that has `outer_perm`
pub fn adjust_perm(outer_perm: &Perm, inner_perm: &Perm) -> Perm {
    match outer_perm {
        Perm::My => inner_perm.clone(),
        Perm::Shared(places) => match inner_perm {
            Perm::My => outer_perm.clone(),
            Perm::Shared(_) => inner_perm.clone(),
            Perm::Leased(_) => outer_perm.clone(),
            Perm::Var(_) => todo!(),
        },
        Perm::Leased(_) => match inner_perm {
            Perm::My => outer_perm.clone(),
            Perm::Shared(_) => inner_perm.clone(),
            Perm::Leased(_) => outer_perm.clone(),
            Perm::Var(_) => todo!(),
        },
        Perm::Var(_) => todo!(),
    }
}

fn merge_places(places: &[Place], places1: &[Place]) -> Vec<Place> {
    places.iter().chain(places1).cloned().collect()
}

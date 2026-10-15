use formality_core::{cast_impl, DowncastTo, UpcastFrom};

use crate::core::grammar as core;

use super::{NamedTy, Parameter, Ty, TypeName};

impl UpcastFrom<TypeName> for NamedTy {
    fn upcast_from(name: TypeName) -> Self {
        NamedTy {
            name,
            parameters: vec![],
        }
    }
}

impl DowncastTo<TypeName> for NamedTy {
    fn downcast_to(&self) -> Option<TypeName> {
        self.parameters.is_empty().then(|| self.name.clone())
    }
}

cast_impl!((TypeName) <: (NamedTy) <: (Ty));
cast_impl!((NamedTy) <: (Ty) <: (Parameter));

// Both ASTs use the core language's binding infrastructure. Derived folding of a
// surface type variable therefore receives a core Parameter. Structurally lift
// that substitution so opening/rebinding a surface binder never reparses text.
impl DowncastTo<Ty> for core::Parameter {
    fn downcast_to(&self) -> Option<Ty> {
        match self {
            core::Parameter::Ty(ty) => Some(lift_type(ty)),
            core::Parameter::Perm(_) => None,
        }
    }
}

fn lift_type(ty: &core::Ty) -> Ty {
    match ty {
        core::Ty::NamedTy(ty) => Ty::NamedTy(NamedTy {
            name: ty.name.clone(),
            parameters: ty.parameters.iter().map(lift_parameter).collect(),
        }),
        core::Ty::Var(var) => Ty::Var(*var),
        core::Ty::ApplyPerm(perm, ty) => {
            Ty::ApplyPerm(perm.clone(), std::sync::Arc::new(lift_type(ty)))
        }
    }
}

fn lift_parameter(parameter: &core::Parameter) -> Parameter {
    match parameter {
        core::Parameter::Ty(ty) => Parameter::Ty(lift_type(ty)),
        core::Parameter::Perm(perm) => Parameter::Perm(perm.clone()),
    }
}

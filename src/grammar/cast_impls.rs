use super::*;
use formality_core::cast_impl;

cast_impl!((BoundVar) <: (Variable) <: (Ty));
cast_impl!((BoundVar) <: (Ty) <: (Parameter));

cast_impl!((ExistentialVar) <: (Variable) <: (Ty));
cast_impl!((ExistentialVar) <: (Ty) <: (Parameter));

cast_impl!((UniversalVar) <: (Variable) <: (Ty));
cast_impl!((UniversalVar) <: (Ty) <: (Parameter));

cast_impl!((Variable) <: (Ty) <: (Parameter));

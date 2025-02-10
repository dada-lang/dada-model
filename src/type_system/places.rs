use formality_core::{Fallible, Upcast};

use crate::{
    grammar::{ClassDeclBoundData, FieldDecl, NamedTy, Place, Projection, Ty, TypeName},
    type_system::env::Env,
};

use super::in_flight::InFlight;

impl Env {
    pub fn place_ty(&self, place: &Place) -> Fallible<Ty> {
        let Place { var, projections } = place;
        let var_ty = self.var_ty(var)?;
        let ty = self.type_projections(&var.upcast(), var_ty, &projections)?;
        Ok(ty)
    }

    /// Returns a list of the fields of the given `place`, with types adjusted
    /// due to the permissions from `place`.
    pub fn place_fields(&self, place: &Place) -> Fallible<Vec<FieldDecl>> {
        let place_ty = self.place_ty(place)?;
        self.fields(&place_ty)
    }

    /// Given a place `place`, returns the type of the field that is
    /// selected by the last projection of `place`, as well as the type
    /// of the value that owns that field.
    ///
    /// For example, if `place` is `x.f.g`, then this returns `(x, G)`
    /// where `G` is the type of the field `G` as declared in the struct
    /// (the `this` place is replaced with `x.f`).
    ///
    /// If `place` is a variable, then this returns `(None, var_ty)`.
    ///
    /// This is used to type assignments.
    pub fn owner_and_field_ty(&self, place: &Place) -> Fallible<(Option<Ty>, Ty)> {
        let Some(last_proj) = place.projections.last() else {
            let var_ty = self.var_ty(&place.var)?;
            return Ok((None, var_ty.clone()));
        };

        let owner_place = place.owner().unwrap();
        let owner_ty = self.place_ty(&owner_place)?;
        let proj_ty =
            self.type_projections(&owner_place, &owner_ty.strip_perm(), &[last_proj.clone()])?;
        Ok((Some(owner_ty), proj_ty))
    }

    fn type_projections(
        &self,
        place: &Place,
        var_ty: &Ty,
        projections: &[Projection],
    ) -> Fallible<Ty> {
        let Some((proj0, projs)) = projections.split_first() else {
            return Ok(var_ty.clone());
        };

        match proj0 {
            Projection::Field(field_id) => {
                let fields = self.fields(var_ty)?;
                let field =
                    fields
                        .iter()
                        .find(|field| field.name == *field_id)
                        .ok_or(anyhow::anyhow!(
                            "field `{field_id:?}` not found in type `{var_ty:?}` (found: {:?})",
                            fields.iter().map(|f| &f.name).collect::<Vec<_>>(),
                        ))?;
                let field_ty = field.ty.with_this_stored_to(&place);
                let field_place = place.project(proj0);
                self.type_projections(&field_place, &field_ty, projs)
            }
        }
    }

    pub fn fields(&self, ty: &Ty) -> Fallible<Vec<FieldDecl>> {
        match ty {
            Ty::NamedTy(NamedTy {
                name: TypeName::Id(id),
                parameters,
            }) => {
                let class_decl = self.program().class_named(&id)?;
                let ClassDeclBoundData {
                    predicates: _,
                    fields,
                    methods: _,
                } = class_decl.binder.instantiate_with(&parameters).unwrap();
                Ok(fields)
            }
            Ty::NamedTy(NamedTy {
                name: TypeName::Tuple(_),
                parameters: _,
            }) => anyhow::bail!("tuple fields not implemented"),
            Ty::NamedTy(NamedTy {
                name: TypeName::Int,
                parameters: _,
            }) => Ok(vec![]),
            Ty::Var(_) => Ok(vec![]),
            Ty::ApplyPerm(perm, ty) => {
                let fields = self.fields(ty)?;
                let fields_with_perm: Vec<FieldDecl> = fields
                    .into_iter()
                    .map(|field| FieldDecl {
                        ty: Ty::apply_perm(perm, field.ty),
                        atomic: field.atomic,
                        name: field.name,
                    })
                    .collect();
                Ok(fields_with_perm)
            }
            Ty::Or(..) => anyhow::bail!("or fields not implemented"),
        }
    }
}

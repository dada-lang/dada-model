use formality_core::{judgment_fn, Cons};

use crate::{
    grammar::{ClassDeclBoundData, FieldDecl, FieldId, NamedTy, Place, Projection, Ty, TypeName},
    type_system::{env::Env, in_flight::InFlight},
};

judgment_fn! {
    /// Returns the type of the value in the place.
    pub fn place_ty(
        env: Env,
        place: Place,
    ) => Ty {
        debug(place, env)

        (
            (let var_ty = env.var_ty(&var)?)
            (type_projections(&env, &var, var_ty, &projections) => ty)
            ----------------------------------- ("place")
            (place_ty(env, Place { var, projections }) => ty)
        )
    }
}

judgment_fn! {
    /// For a place that is going to be assigned, returns a pair (o, f) where
    ///
    /// * `o` is the type of the object owning the field (and hence must be
    ///   uniquely accessible);
    /// * `f` is the type of the field that will be assigned to (and hence the
    ///   type of the value to be assigned must be a subtype of `f`).
    ///
    /// When `place` represents a single variable, the owner type is unit.
    /// This is a hack but unit happens to have the requisite properties.
    pub fn owner_and_field_ty(
        env: Env,
        place: Place,
    ) => (Ty, Ty) {
        debug(place, env)

        (
            (if projections.is_empty())!
            (let var_ty = env.var_ty(&var)?)
            ----------------------------------- ("var")
            (owner_and_field_ty(env, Place { var, projections }) => (Ty::unit(), var_ty))
        )

        (
            (if let Some(Projection::Field(field_id)) = place.projections.last())!
            (if let Some(owner_place) = place.owner())
            (place_ty(&env, owner_place) => owner_ty)
            (field_ty(&env, owner_ty.strip_perm(), field_id) => field_ty)
            ----------------------------------- ("field")
            (owner_and_field_ty(env, place) => (&owner_ty, field_ty))
        )
    }
}

judgment_fn! {
    pub fn place_fields(
        env: Env,
        place: Place,
    ) => Vec<FieldDecl> {
        debug(place, env)

        (
            (place_ty(&env, &place) => ty)
            (fields(&env, ty) => fields)
            ----------------------------------- ("place")
            (place_fields(env, place) => fields.with_this_stored_to(&place))
        )
    }
}

judgment_fn! {
    fn type_projections(
        env: Env,
        base_place: Place,
        base_ty: Ty,
        projections: Vec<Projection>,
    ) => Ty {
        debug(base_place, base_ty, projections, env)

        (
            ----------------------------------- ("nil")
            (type_projections(_env, _base_place, base_ty, ()) => base_ty)
        )

        (
            (field_ty(&env, base_ty, &field_name) => ty)
            (let ty = ty.with_this_stored_to(&base_place))
            (type_projections(&env, base_place.project(&field_name), ty, &projections) => ty)
            ----------------------------------- ("field")
            (type_projections(env, base_place, base_ty, Cons(Projection::Field(field_name), projections)) => ty)
        )
    }
}

judgment_fn! {
    fn field_ty(
        env: Env,
        base_ty: Ty,
        field: FieldId,
    ) => Ty {
        debug(base_ty, field, env)

        (
            (fields(env, ty) => fields)
            (fields => field)
            (if field.name == field_name)
            ----------------------------------- ("field")
            (field_ty(env, ty, field_name) => field.ty)
        )
    }
}

judgment_fn! {
    fn fields(
        env: Env,
        base_ty: Ty,
    ) => Vec<FieldDecl> {
        debug(base_ty, env)

        (
            (env.program().class_named(&id) => class_decl)
            (let ClassDeclBoundData { fields, methods: _ } = class_decl.binder.instantiate_with(&parameters).unwrap())
            ----------------------------------- ("named-ty")
            (fields(_env, NamedTy { name: TypeName::Id(id), parameters }) => fields)
        )

        (
            (fields(env, &*ty) => fields)
            (let fields_with_perm: Vec<FieldDecl> = fields.into_iter().map(|field| FieldDecl {
                ty: Ty::apply_perm(&perm, field.ty),
                atomic: field.atomic,
                name: field.name
            }).collect())
            ----------------------------------- ("apply-perm")
            (fields(env, Ty::ApplyPerm(perm, ty)) => fields_with_perm)
        )
    }
}

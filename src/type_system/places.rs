use std::sync::Arc;

use formality_core::{judgment_fn, Cons};

use crate::{
    grammar::{ClassDeclBoundData, FieldId, NamedTy, Place, Projection, Ty, TypeName},
    type_system::{env::Env, in_flight::InFlight},
};

judgment_fn! {
    pub fn place_ty(
        env: Env,
        place: Place,
    ) => Ty {
        debug(place, env)

        (
            (env.var_ty(&var) => var_ty)
            (type_projections(&env, &var, var_ty, &projections) => ty)
            ----------------------------------- ("place")
            (place_ty(env, Place { var, projections }) => ty)
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
            (env.program().class_named(&id) => class_decl)
            (let ClassDeclBoundData { fields, methods: _ } = class_decl.binder.instantiate_with(&parameters).unwrap())
            (fields => field)
            (if field.name == field_name)
            ----------------------------------- ("field")
            (field_ty(_env, NamedTy { name: TypeName::Id(id), parameters }, field_name) => field.ty)
        )

        (
            (field_ty(env, &*ty, field_name) => field_ty)
            ----------------------------------- ("field")
            (field_ty(env, Ty::ApplyPerm(perm, ty), field_name) => Ty::apply_perm(&perm, Arc::new(field_ty)))
        )
    }
}

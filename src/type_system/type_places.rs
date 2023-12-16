use std::sync::Arc;

use formality_core::judgment_fn;

use crate::{
    grammar::{ClassDeclBoundData, ClassName, ClassTy, FieldId, Place, Projection, Ty},
    type_system::{env::Env, quantifiers::fold},
};

judgment_fn! {
    pub fn place_ty(
        env: Env,
        place: Place,
    ) => Ty {
        debug(place, env)

        (
            (env.var_ty(var) => var_ty)
            (fold(var_ty.clone(), &projections, &|base_ty, projection| type_projection(&env, base_ty, projection)) => ty)
            ----------------------------------- ("place")
            (place_ty(env, Place { var, projections }) => ty)
        )
    }
}

judgment_fn! {
    fn type_projection(
        env: Env,
        base_ty: Ty,
        projection: Projection,
    ) => Ty {
        debug(base_ty, projection, env)

        (
            (field_ty(env, base_ty, field_name) => ty)
            ----------------------------------- ("field")
            (type_projection(env, base_ty, Projection::Field(field_name)) => ty)
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
            (field_ty(_env, ClassTy { name: ClassName::Id(id), parameters }, field_name) => field.ty)
        )

        (
            (field_ty(env, &*ty, field_name) => field_ty)
            ----------------------------------- ("field")
            (field_ty(env, Ty::ApplyPerm(perm, ty), field_name) => Ty::apply_perm(&perm, Arc::new(field_ty)))
        )
    }
}

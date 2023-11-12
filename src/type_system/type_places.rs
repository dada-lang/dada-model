use formality_core::judgment_fn;

use crate::{
    grammar::{ClassDeclBoundData, ClassName, ClassTy, FieldId, Place, Program, Projection, Ty},
    type_system::{env::Env, quantifiers::fold},
};

judgment_fn! {
    pub fn type_place(
        program: Program,
        env: Env,
        place: Place,
    ) => Ty {
        debug(place, program, env)

        (
            (env.var_ty(var) => var_ty)
            (fold(var_ty.clone(), &projections, &|base_ty, projection| type_projection(&program, &env, base_ty, projection)) => ty)
            ----------------------------------- ("place")
            (type_place(program, env, Place { var, projections }) => ty)
        )
    }
}

judgment_fn! {
    fn type_projection(
        program: Program,
        env: Env,
        base_ty: Ty,
        projection: Projection,
    ) => Ty {
        debug(base_ty, projection, program, env)

        (
            (field_ty(program, env, base_ty, field_name) => ty)
            ----------------------------------- ("field")
            (type_projection(program, env, base_ty, Projection::Field(field_name)) => ty)
        )
    }
}

judgment_fn! {
    fn field_ty(
        program: Program,
        env: Env,
        base_ty: Ty,
        field: FieldId,
    ) => Ty {
        debug(base_ty, field, program, env)

        (
            (program.class_named(&id) => class_decl)
            (let ClassDeclBoundData { fields } = class_decl.binder.instantiate_with(&parameters).unwrap())
            (fields.into_iter() => field)
            (if field.name == field_name)
            ----------------------------------- ("field")
            (field_ty(program, env, ClassTy { name: ClassName::Id(id), parameters }, field_name) => field.ty)
        )
    }
}

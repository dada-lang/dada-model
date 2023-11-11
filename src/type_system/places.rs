use formality_core::judgment_fn;

use crate::{
    grammar::{ClassTy, Place, Program, Projection, Ty},
    type_system::env::Env,
};

judgment_fn! {
    pub fn check_place(
        program: Program,
        env: Env,
        place: Place,
    ) => () {
        debug(place, program, env)

        (
            (env.var_ty(var) => ty)

            ----------------------------------- ("var")
            (check_place(program, env, Place { var, projections }) => ())
        )
    }
}

judgment_fn! {
    fn check_projection(
        program: Program,
        env: Env,
        base_ty: Ty,
        projection: Projection,
    ) => Ty {
        debug(base_ty, projection, program, env)

        (
            ----------------------------------- ("field")
            (check_projection(program, env, base_ty, Projection::Field(field_name)) => ty)
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
        debug(base_ty, projection, program, env)

        (
            ----------------------------------- ("field")
            (field_ty(program, env, ClassTy { perm, name, parameters }, field_name) => ty)
        )
    }
}

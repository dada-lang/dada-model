use formality_core::judgment_fn;

use crate::{
    grammar::{Place, Program, Projection, Ty},
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
            (env.var_ty(var) => ty)
            (if let Some(ClassTy {}) = ty.downcast())
            ----------------------------------- ("var")
            (check_projection(program, env, Place { var, projections }) => ty)
        )
    }
}

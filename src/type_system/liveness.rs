//! We do something really dumb and brute force to manage liveness.
//! Basically, in between every statement, we have the option of making
//! initialized variables be considered moved. Note that this could cause
//! type check errors later on if that variable is used again. In "real life"
//! we would use a liveness check to detect that possibility, but to keep
//! these rules simple, we let the judgments just explore all possibilities.

use formality_core::judgment_fn;

use crate::{
    grammar::{Access, LocalVariableDecl},
    type_system::{accesses::env_permits_access, env::Env, flow::Flow},
};

judgment_fn! {
    pub fn adjust_for_liveness(
        env: Env,
        flow: Flow,
    ) => (Env, Flow) {
        debug(env, flow)

        (
            ----------------------------------------- ("no changes")
            (adjust_for_liveness(env, flow) => (env, flow))
        )


        (
            (env.local_variables() => LocalVariableDecl { name, ty: _ })
            (if !flow.variable_uninitialized(&name))
            (env_permits_access(&env, &flow, Access::Give, &name) => (env, flow))!
            (let flow = flow.uninitialize_var(&name))
            (adjust_for_liveness(env, flow) => (env, flow))
            ----------------------------------------- ("drop variable")
            (adjust_for_liveness(env, flow) => (env, flow))
        )
    }
}

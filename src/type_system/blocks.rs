use formality_core::judgment_fn;

use crate::{
    grammar::{Block, Ty, Var},
    type_system::{
        env::Env,
        liveness::LivePlaces,
        pop_normalize::normalize_ty_for_pop,
        statements::type_statements,
    },
};

judgment_fn! {
    pub fn type_block(
        env: Env,
        live_after: LivePlaces,
        block: Block,
    ) => (Env, Ty) {
        debug(block, env, live_after)

        (
            // Snapshot the set of local variables before the block.
            (let vars_before = env.local_variable_names())

            (type_statements(env, live_after, statements) => (env, ty))

            // Identify block-scoped variables (introduced during the block).
            (let vars_after = env.local_variable_names())
            (let block_vars: Vec<Var> = vars_after.iter().filter(|v| !vars_before.contains(v)).cloned().collect())

            // Normalize the result type against block-scoped variables.
            // This resolves permissions referencing block-locals that are about to be popped.
            // Dangling borrows (ref/mut from owned block-locals) are detected here.
            (let ty = normalize_ty_for_pop(&env, &live_after, &ty, &block_vars)?)

            // Pop block-scoped variables from the env.
            (let env = env.pop_block_variables(block_vars)?)

            ----------------------------------- ("place")
            (type_block(env, live_after, Block { statements }) => (env, ty))
        )
    }
}

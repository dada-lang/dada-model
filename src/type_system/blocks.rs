use formality_core::judgment_fn;

use crate::{
    grammar::{Block, Ty},
    type_system::{env::Env, liveness::LivePlaces, statements::type_statements},
};

judgment_fn! {
    pub fn type_block(
        env: Env,
        live_after: LivePlaces,
        block: Block,
    ) => (Env, Ty) {
        debug(block, env, live_after)

        (
            (type_statements(env, live_after, statements) => (env, ty))
            ----------------------------------- ("place")
            (type_block(env, live_after, Block { statements }) => (env, ty))
        )
    }
}

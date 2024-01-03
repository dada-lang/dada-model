use formality_core::judgment_fn;

use crate::{
    grammar::{Block, Ty},
    type_system::{env::Env, flow::Flow, liveness::LiveVars, statements::type_statements},
};

judgment_fn! {
    pub fn type_block(
        env: Env,
        flow: Flow,
        live_after: LiveVars,
        block: Block,
    ) => (Env, Flow, Ty) {
        debug(block, env, flow, live_after)

        (
            (type_statements(env, flow, live_after, statements) => (env, flow, ty))
            ----------------------------------- ("place")
            (type_block(env, flow, live_after, Block { statements }) => (env, flow, ty))
        )
    }
}

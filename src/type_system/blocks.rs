use formality_core::judgment_fn;

use crate::{
    grammar::{Block, Ty},
    type_system::{env::Env, flow::Flow, statements::type_statements},
};

judgment_fn! {
    pub fn type_block(
        env: Env,
        flow: Flow,
        block: Block,
    ) => (Env, Flow, Ty) {
        debug(block, env, flow)

        (
            (type_statements(env, flow, statements) => (env, flow, ty))
            ----------------------------------- ("place")
            (type_block(env, flow, Block { statements }) => (env, flow, ty))
        )
    }
}

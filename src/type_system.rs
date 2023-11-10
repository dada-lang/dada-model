use formality_core::{judgment_fn, term};

use crate::grammar::VariableDecl;

#[term]
struct Env {
    variables: Vec<VariableDecl>,
}

mod program;
mod quantifiers;

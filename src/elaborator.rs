//! Elaboration: an *elaborated* program has various unspoken defaults applied to it.
//!
//! The only way to construct an [`ElaboratedProgram`] is via [`ElaboratedProgram::elaborate`],
//! which runs the (currently no-op) [`elaborate`] pass. Storing an `ElaboratedProgram`
//! in `Env` and the interpreter therefore proves that elaboration has taken place.

use std::ops::Deref;
use std::sync::Arc;

use crate::grammar::Program;

/// A program that has had elaboration applied. The only way to construct one
/// is via [`ElaboratedProgram::elaborate`], which guarantees the private
/// [`elaborate`] pass has run. This is *not* a `#[term]` — we hand-implement
/// the traits we need so no auto-generated constructor can bypass elaboration.
#[derive(Clone, Ord, Eq, PartialEq, PartialOrd, Hash)]
pub struct ElaboratedProgram {
    program: Arc<Program>,
}

formality_core::cast_impl!(ElaboratedProgram);

impl ElaboratedProgram {
    /// Elaborate `program` (apply syntactic defaults) and wrap the result.
    /// This is the only way to obtain an `ElaboratedProgram`.
    pub fn elaborate(program: &Program) -> Self {
        let mut program = program.clone();
        elaborate(&mut program);
        Self {
            program: Arc::new(program),
        }
    }
}

impl std::fmt::Debug for ElaboratedProgram {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Elide the actual program because it's really repetitive in debug output
        f.debug_struct("ElaboratedProgram").finish_non_exhaustive()
    }
}

impl Deref for ElaboratedProgram {
    type Target = Program;

    fn deref(&self) -> &Program {
        &self.program
    }
}

/// Apply syntactic defaults to `program` in place. Currently a no-op.
fn elaborate(_program: &mut Program) {
    /* no-op for now */
}

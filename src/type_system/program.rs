use crate::grammar::{Decl, Program};

use super::quantifiers::for_all;
use formality_core::judgment_fn;

judgment_fn! {
    pub fn check_program(
        program: Program,
    ) => ()
    {
        debug(program)

        (
            (for_all(&program.decls, |d: Decl| check_decl(&program, d)) => _)
            -------------------- ("program-ok")
            (check_program(program) => ())
        )
    }
}

judgment_fn! {
    fn check_decl(
        program: Program,
        decl: Decl,
    ) => ()
    {
        debug(decl, program)

        (
            -------------------- ("decl-ok")
            (check_decl(_program, _decl) => ())
        )
    }
}

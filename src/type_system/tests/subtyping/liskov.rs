//! ## Liskov Substitution Principle (LSP)
//!
//! The "Liskov Substitution Principle" is that if T1 <: T2, then a value of type T1 can be
//! substituted for a value of type T2 and nothing can go wrong. This module aims to systematically
//! explore the various substitution considerations relevant to Dada:
//!
//! * [Compatible layout](`compatible_layout`): the most basic is that the layout of the data structure in memory must be compatible.
//!   This is affected by the permisssion since `leased` structures are represented by pointers but everything
//!   else is by-value.
//! * [Permission](`subpermission`): All operations permitted by supertype must be permitted by the subtype.
//! * [Liveness and cancellation](`cancellation`)
//!   * When variables are dead, subtyping allows for *cancellation*, so e.g. if `d1` is dead,
//!     then `shared{d1} leased{d2} Foo` is a subtype of `leased{d2} Foo`.

use crate::{
    dada_lang::term,
    grammar::{Perm, Ty},
    type_system::check_program,
};
use formality_core::{test, test_util::ResultTestExt};
mod cancellation;
mod compatible_layout;
mod subpermission;

#[test]
fn liskov_rules() {
    let program_template = "
        class Data {
            left: my Data;
            right: my Data;
        }
        class Main {
            fn test[perm M, perm C](
                my self,
                my_d1: my Data,
                my_d2: my Data,
                my_d3: my Data,
                src: {subperm} Data,
            )
            where
                copy(C),
            {
                let dst: {supperm} Data = src.give;
            }
        }
    ";

    let liskov_rules = &[
        ("my", "my", "✅"),
        ("my", "our", "✅"),
        ("my", "shared{my_d1}", "✅"),
        ("my", "leased{my_d1}", "❌"),
        ("my", "our leased{my_d1}", "✅"),
        ("my", "C", "✅"),
        ("my", "M", "❌"),
        ("our", "my", "❌"),
        ("our", "our", "✅"),
        ("our", "shared{my_d1}", "✅"),
        ("our", "leased{my_d1}", "❌"),
        ("our", "our leased{my_d1}", "✅"),
        ("our", "C", "✅"),
        ("our", "M", "❌"),
        ("shared{my_d1}", "my", "❌"),
        ("shared{my_d1}", "our", "❌"),
        ("shared{my_d1}", "shared{my_d1}", "✅"),
        ("shared{my_d1}", "leased{my_d1}", "❌"),
        ("shared{my_d1}", "our leased{my_d1}", "❌"),
        ("shared{my_d1}", "C", "❌"),
        ("shared{my_d1}", "M", "❌"),
        ("leased{my_d1}", "my", "❌"),
        ("leased{my_d1}", "our", "❌"),
        ("leased{my_d1}", "shared{my_d1}", "❌"),
        ("leased{my_d1}", "leased{my_d1}", "✅"),
        ("leased{my_d1}", "our leased{my_d1}", "❌"),
        ("leased{my_d1}", "C", "❌"),
        ("leased{my_d1}", "M", "❌"),
        ("our leased{my_d1}", "my", "❌"),
        ("our leased{my_d1}", "our", "❌"),
        ("our leased{my_d1}", "shared{my_d1}", "❌"),
        ("our leased{my_d1}", "leased{my_d1}", "❌"),
        ("our leased{my_d1}", "our leased{my_d1}", "✅"),
        ("our leased{my_d1}", "C", "❌"),
        ("our leased{my_d1}", "M", "❌"),
        ("C", "my", "❌"),
        ("C", "our", "❌"),
        ("C", "shared{my_d1}", "❌"),
        ("C", "leased{my_d1}", "❌"),
        ("C", "our leased{my_d1}", "❌"),
        ("C", "C", "✅"),
        ("C", "M", "❌"),
        ("M", "my", "❌"),
        ("M", "our", "❌"),
        ("M", "shared{my_d1}", "❌"),
        ("M", "leased{my_d1}", "❌"),
        ("M", "our leased{my_d1}", "❌"),
        ("M", "C", "❌"),
        ("M", "M", "✅"),
    ];

    for &(subperm, supperm, outcome) in liskov_rules {
        eprintln!("# {subperm} <: {supperm} should be {outcome}");

        let program = program_template
            .replace("{subperm}", subperm)
            .replace("{supperm}", supperm);

        let result = check_program(&term(&program));

        let expected_str = "judgment `type_expr_as { expr: src . give, as_ty:";

        match (outcome, result) {
            ("✅", result) => result.assert_ok(expect_test::expect![["()"]]),
            ("❌", Ok(_)) => panic!("unexpected subtyping: expected {subperm} not to be a subperm of {supperm}, but it was!"),
            ("❌", Err(s)) => if !format!("{s:?}").contains(expected_str) {
                panic!("subtyping failed but error did not contain {expected_str:?}:\n{s:?}");
            }
            (_, _) => panic!("bad table, expected emoji for outcome"),
        }
    }
}

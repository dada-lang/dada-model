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
//!     then `shared[d1] leased[d2] Foo` is a subtype of `leased[d2] Foo`.

use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};
mod cancellation;
mod compatible_layout;
mod subpermission;

enum Template {
    Sub(&'static str, &'static str, &'static str),
    With(&'static str, &'static [Template], &'static str),
}
use Template::*;

const D1D2_MY_DATA: &str = "
    class Data {
        left: my Data;
        right: my Data;
    }
    class Main {
        fn test[perm M, perm C](
            my self,

            d1: my Data,
            d2: my Data,
        )
        where
            copy(C),
        {
            {PREFIX}

            let src: {SUBPERM} Data = !;
            let dst: {SUPPERM} Data = src.give;

            {SUFFIX}
        }
    }
";

#[test]
fn liskov_rules() {
    run_rules_against_templates(
        D1D2_MY_DATA,
        &[
            Sub("my", "my", "✅"),
            Sub("my", "our", "✅"),
            Sub("my", "shared[d1]", "✅"),
            Sub("my", "shared[d1, d2]", "✅"),
            Sub("my", "shared[d2]", "✅"),
            Sub("my", "leased[d1]", "❌"),
            Sub("my", "leased[d1, d2]", "❌"),
            Sub("my", "leased[d2]", "❌"),
            Sub("my", "our leased[d1]", "✅"),
            Sub("my", "C", "✅"),
            Sub("my", "M", "❌"),
            Sub("our", "my", "❌"),
            Sub("our", "our", "✅"),
            Sub("our", "shared[d1]", "✅"),
            Sub("our", "shared[d1, d2]", "✅"),
            Sub("our", "shared[d2]", "✅"),
            Sub("our", "leased[d1]", "❌"),
            Sub("our", "leased[d1, d2]", "❌"),
            Sub("our", "leased[d2]", "❌"),
            Sub("our", "our leased[d1]", "✅"),
            Sub("our", "C", "✅"),
            Sub("our", "M", "❌"),
            Sub("shared[d1]", "my", "❌"),
            Sub("shared[d1]", "our", "❌"),
            Sub("shared[d1]", "shared[d1]", "✅"),
            Sub("shared[d1]", "shared[d1, d2]", "✅"),
            Sub("shared[d1]", "shared[d2]", "❌"),
            Sub("shared[d1]", "leased[d1]", "❌"),
            Sub("shared[d1]", "leased[d1, d2]", "❌"),
            Sub("shared[d1]", "leased[d2]", "❌"),
            Sub("shared[d1]", "our leased[d1]", "❌"),
            Sub("shared[d1]", "C", "❌"),
            Sub("shared[d1]", "M", "❌"),
            Sub("leased[d1]", "my", "❌"),
            Sub("leased[d1]", "our", "❌"),
            Sub("leased[d1]", "shared[d1]", "❌"),
            Sub("leased[d1]", "shared[d1, d2]", "❌"),
            Sub("leased[d1]", "shared[d2]", "❌"),
            Sub("leased[d1]", "leased[d1]", "✅"),
            Sub("leased[d1]", "leased[d1, d2]", "✅"),
            Sub("leased[d1]", "leased[d2]", "❌"),
            Sub("leased[d1]", "our leased[d1]", "❌"),
            Sub("leased[d1]", "C", "❌"),
            Sub("leased[d1]", "M", "❌"),
            Sub("our leased[d1]", "my", "❌"),
            Sub("our leased[d1]", "our", "❌"),
            Sub("our leased[d1]", "shared[d1]", "❌"),
            Sub("our leased[d1]", "shared[d1, d2]", "❌"),
            Sub("our leased[d1]", "shared[d2]", "❌"),
            Sub("our leased[d1]", "leased[d1]", "❌"),
            Sub("our leased[d1]", "leased[d1, d2]", "❌"),
            Sub("our leased[d1]", "leased[d2]", "❌"),
            Sub("our leased[d1]", "our leased[d1]", "✅"),
            Sub("our leased[d1]", "our leased[d1, d2]", "✅"),
            Sub("our leased[d1]", "our leased[d2]", "❌"),
            Sub("our leased[d1]", "C", "❌"),
            Sub("our leased[d1]", "M", "❌"),
            Sub("C", "my", "❌"),
            Sub("C", "our", "❌"),
            Sub("C", "shared[d1]", "❌"),
            Sub("C", "leased[d1]", "❌"),
            Sub("C", "our leased[d1]", "❌"),
            Sub("C", "C", "✅"),
            Sub("C", "M", "❌"),
            Sub("M", "my", "❌"),
            Sub("M", "our", "❌"),
            Sub("M", "shared[d1]", "❌"),
            Sub("M", "leased[d1]", "❌"),
            Sub("M", "our leased[d1]", "❌"),
            Sub("M", "C", "❌"),
            Sub("M", "M", "✅"),
            With(
                "let dld1 = d1.lease;\
                 let dld2 = d2.lease;\
                 let dl1 = dld1.lease;\
                 let dl2 = dld2.lease;",
                &[
                    Sub("leased[dl1]", "leased[dl1]", "✅"),
                    Sub("leased[dl1]", "leased[dl1, dl2]", "✅"),
                    Sub("leased[dl1]", "leased[dl2]", "❌"),
                    Sub("leased[dl1]", "leased[dl1] shared[dld1]", "❌"),
                    Sub("leased[dl1]", "leased[dl1] leased[dld1]", "✅"),
                    Sub("leased[dl1]", "leased[dl1] leased[dld1, dld2]", "✅"),
                    Sub("leased[dl1]", "leased[dld1]", "✅"), // because dl1 is dead
                    Sub("leased[dl1]", "leased[dld1, dld2]", "✅"), // because dl1 is dead
                    Sub("leased[dl1]", "leased[dld2] leased[dld1]", "✅"), // equiv to leased[dld1, dld2]
                    Sub("leased[dl1]", "leased[dld2]", "❌"), // dl1 is dead but it came from dld1, not dld2
                    Sub("leased[dl1]", "leased[dl2] leased[dl2]", "❌"), // dl1 is dead but it came from dld1, not dl2
                ],
                "let _dld1 = dld1.give;\
                 let _dld2 = dld2.give;",
            ),
            With(
                "let dld1 = d1.lease;\
                 let dld2 = d2.lease;\
                 let dl1 = dld1.lease;\
                 let dl2 = dld2.lease;",
                &[
                    Sub("leased[dl1]", "leased[dl1]", "✅"),
                    Sub("leased[dl1]", "leased[dl1, dl2]", "✅"),
                    Sub("leased[dl1]", "leased[dl2]", "❌"),
                    Sub("leased[dl1]", "leased[dl1] shared[dld1]", "❌"),
                    Sub("leased[dl1]", "leased[dl1] leased[dld1]", "✅"),
                    Sub("leased[dl1]", "leased[dl1] leased[dld1, dld2]", "✅"),
                    Sub("leased[dl1]", "leased[dld1]", "❌"), // because dl1 is not dead
                    Sub("leased[dl1]", "leased[dld1, dld2]", "❌"), // because dl1 is not dead
                    Sub("leased[dl1]", "leased[dld2]", "❌"),
                    Sub("leased[dl1]", "leased[dld2] leased[dld1]", "❌"),
                    Sub("leased[dl1]", "leased[dl2] leased[dl2]", "❌"),
                ],
                "let _dl1 = dl1.give;\
                 let _dl2 = dl2.give;\
                 let _dld1 = dld1.give;\
                 let _dld2 = dld2.give;",
            ),
        ],
    );
}

#[test]
fn liskov_rules_nested() {
    run_rules_against_templates(
        D1D2_MY_DATA,
        &[With(
            "let d1l = d1.lease;\
                 let d1ll = d1l.lease;\
                 let d1lll = d1ll.lease;",
            &[
                Sub("leased[d1lll]", "leased[d1]", "✅"), // because d1lll is dead
            ],
            "",
        )],
    );
}

const PAIR_LEASED: &str = "
        class Pair {
            a: my Data;
            b: my Data;
        }
        class Data { }
        class Main {
            fn test[perm P](my self, pair: P Pair) where leased(P) {
                {PREFIX}

                let src: {SUBPERM} = !;
                let dst: {SUPPERM} = src.give;

                {SUFFIX}
            }

            fn consume_from_a[perm P](my self, pair: P Pair, from_a: leased[pair.a] Data) where leased(P) { (); }
            fn consume_from_b[perm P](my self, pair: P Pair, from_b: leased[pair.b] Data) where leased(P) { (); }
        }
        ";

#[test]
fn liskov_from_pair_leased() {
    run_rules_against_templates(
        PAIR_LEASED,
        &[
            // In these tests, `pair` is live.
            With(
                "let d1: leased[pair.a] Data = pair.a.lease; \
                 let d2: leased[pair.b] Data = pair.b.lease;",
                &[
                    Sub("leased[d1] Data", "leased[d2] Data", "❌"),
                    Sub("leased[d1] Data", "leased[d1] Data", "✅"),
                    Sub("leased[d1] Data", "leased[d1, d2] Data", "✅"),
                    Sub("leased[d1] Data", "leased[pair.a] Data", "✅"),
                    Sub("leased[d1] Data", "leased[pair.b] Data", "❌"),
                    Sub("leased[d1] Data", "leased[pair] Data", "✅"),
                    Sub("leased[d1] Data", "leased[pair.a, pair.b] Data", "✅"),
                    Sub("leased[d2] Data", "leased[d2] Data", "✅"),
                    Sub("leased[d2] Data", "leased[d1] Data", "❌"),
                    Sub("leased[d2] Data", "leased[d1, d2] Data", "✅"),
                    Sub("leased[d2] Data", "leased[pair.a] Data", "❌"),
                    Sub("leased[d2] Data", "leased[pair.b] Data", "✅"),
                    Sub("leased[d2] Data", "leased[pair] Data", "✅"),
                    Sub("leased[d2] Data", "leased[pair.a, pair.b] Data", "✅"),
                    Sub("leased[d1, d2] Data", "leased[d2] Data", "❌"),
                    Sub("leased[d1, d2] Data", "leased[d1] Data", "❌"),
                    Sub("leased[d1, d2] Data", "leased[d1, d2] Data", "✅"),
                    Sub("leased[d1, d2] Data", "leased[pair.a] Data", "❌"),
                    Sub("leased[d1, d2] Data", "leased[pair.b] Data", "❌"),
                    Sub("leased[d1, d2] Data", "leased[pair] Data", "✅"),
                    Sub("leased[d1, d2] Data", "leased[pair.a, pair.b] Data", "✅"),
                ],
                "let _keep_pair_live = pair.give;",
            ),
            // In these tests, `pair` is dead.
            With(
                "let d1: leased[pair.a] Data = pair.a.lease; \
                 let d2: leased[pair.b] Data = pair.b.lease;",
                &[
                    Sub("leased[d1] Data", "leased[d2] Data", "✅"),
                    Sub("leased[d1] Data", "leased[d1] Data", "✅"),
                    Sub("leased[d1] Data", "leased[d1, d2] Data", "✅"),
                    Sub("leased[d1] Data", "leased[pair.a] Data", "✅"),
                    Sub("leased[d1] Data", "leased[pair.b] Data", "✅"),
                    Sub("leased[d1] Data", "leased[pair] Data", "✅"),
                    Sub("leased[d1] Data", "leased[pair.a, pair.b] Data", "✅"),
                    Sub("leased[d2] Data", "leased[d2] Data", "✅"),
                    Sub("leased[d2] Data", "leased[d1] Data", "✅"),
                    Sub("leased[d2] Data", "leased[d1, d2] Data", "✅"),
                    Sub("leased[d2] Data", "leased[pair.a] Data", "✅"),
                    Sub("leased[d2] Data", "leased[pair.b] Data", "✅"),
                    Sub("leased[d2] Data", "leased[pair] Data", "✅"),
                    Sub("leased[d2] Data", "leased[pair.a, pair.b] Data", "✅"),
                    Sub("leased[d1, d2] Data", "leased[d2] Data", "✅"),
                    Sub("leased[d1, d2] Data", "leased[d1] Data", "✅"),
                    Sub("leased[d1, d2] Data", "leased[d1, d2] Data", "✅"),
                    Sub("leased[d1, d2] Data", "leased[pair.a] Data", "✅"),
                    Sub("leased[d1, d2] Data", "leased[pair.b] Data", "✅"),
                    Sub("leased[d1, d2] Data", "leased[pair] Data", "✅"),
                    Sub("leased[d1, d2] Data", "leased[pair.a, pair.b] Data", "✅"),
                ],
                "",
            ),
        ],
    )
}

fn run_rules_against_templates(base_program: &str, liskov_rules: &[Template]) {
    run_rules_against_templates_with(
        base_program,
        &mut String::new(),
        &mut String::new(),
        liskov_rules,
    );
}

fn run_rules_against_templates_with(
    base_program: &str,
    prefixes: &mut String,
    suffixes: &mut String,
    templates: &[Template],
) {
    for template in templates {
        run_rules_against_template_with(base_program, prefixes, suffixes, template);
    }
}

fn run_rules_against_template_with(
    base_program: &str,
    prefixes: &mut String,
    suffixes: &mut String,
    template: &Template,
) {
    match *template {
        Sub(sub, sup, outcome) => {
            eprintln!("# sub: {sub}, sup: {sup}, outcome: {outcome}");
            let program = base_program
                .replace("{PREFIX}", prefixes)
                .replace("{SUFFIX}", suffixes)
                .replace("{SUBPERM}", sub)
                .replace("{SUPPERM}", sup);

            let result = check_program(&term(&program));

            let expected_str = "judgment `type_expr_as { expr: src . give, as_ty:";

            match (outcome, result) {
                ("✅", result) => result.assert_ok(expect_test::expect![["()"]]),
                ("❌", Ok(_)) => panic!("unexpected subtyping: expected {sub} not to be a subperm of {sup}, but it was!"),
                ("❌", Err(s)) => if !format!("{s:?}").contains(expected_str) {
                    panic!("subtyping failed but error did not contain {expected_str:?}:\n{s:?}");
                }
                (_, _) => panic!("bad table, expected emoji for outcome"),
            }
        }
        With(prefix, templates, suffix) => {
            prefixes.push_str(prefix);
            suffixes.push_str(suffix);
            eprintln!("# prefix: {prefix}, suffix: {suffix} {{");
            run_rules_against_templates_with(base_program, prefixes, suffixes, templates);
            eprintln!("# }}");
            prefixes.truncate(prefixes.len() - prefix.len());
            suffixes.truncate(suffixes.len() - suffix.len());
        }
    }
}

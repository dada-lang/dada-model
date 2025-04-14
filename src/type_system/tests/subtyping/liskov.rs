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
//!     then `ref[d1] mut[d2] Foo` is a subtype of `mut[d2] Foo`.

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
            shared(C),
        {
            {PREFIX}

            let src: {SUBPERM} Data = !;
            let dst: {SUPPERM} Data = src.move;

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
            Sub("my", "ref[d1]", "✅"),
            Sub("my", "ref[d1, d2]", "✅"),
            Sub("my", "ref[d2]", "✅"),
            Sub("my", "mut[d1]", "❌"),
            Sub("my", "mut[d1, d2]", "❌"),
            Sub("my", "mut[d2]", "❌"),
            Sub("my", "our mut[d1]", "✅"),
            Sub("my", "C", "✅"),
            Sub("my", "M", "❌"),
            Sub("our", "my", "❌"),
            Sub("our", "our", "✅"),
            Sub("our", "ref[d1]", "✅"),
            Sub("our", "ref[d1, d2]", "✅"),
            Sub("our", "ref[d2]", "✅"),
            Sub("our", "mut[d1]", "❌"),
            Sub("our", "mut[d1, d2]", "❌"),
            Sub("our", "mut[d2]", "❌"),
            Sub("our", "our mut[d1]", "✅"),
            Sub("our", "C", "✅"),
            Sub("our", "M", "❌"),
            Sub("ref[d1]", "my", "❌"),
            Sub("ref[d1]", "our", "❌"),
            Sub("ref[d1]", "ref[d1]", "✅"),
            Sub("ref[d1]", "ref[d1, d2]", "✅"),
            Sub("ref[d1]", "ref[d2]", "❌"),
            Sub("ref[d1]", "mut[d1]", "❌"),
            Sub("ref[d1]", "mut[d1, d2]", "❌"),
            Sub("ref[d1]", "mut[d2]", "❌"),
            Sub("ref[d1]", "our mut[d1]", "✅"),
            Sub("ref[d1]", "C", "❌"),
            Sub("ref[d1]", "M", "❌"),
            Sub("ref[d1.left]", "ref[d1]", "✅"),
            Sub("ref[d1.right]", "ref[d1]", "✅"),
            Sub("ref[d1.left, d1.right]", "ref[d1]", "✅"),
            Sub("ref[d1]", "ref[d1.left]", "❌"),
            Sub("ref[d1]", "ref[d1.right]", "❌"),
            Sub("ref[d1]", "ref[d1.left, d1.right]", "❌"),
            Sub("mut[d1]", "my", "❌"),
            Sub("mut[d1]", "our", "❌"),
            Sub("mut[d1]", "ref[d1]", "❌"),
            Sub("mut[d1]", "ref[d1, d2]", "❌"),
            Sub("mut[d1]", "ref[d2]", "❌"),
            Sub("mut[d1]", "mut[d1]", "✅"),
            Sub("mut[d1]", "mut[d1, d2]", "✅"),
            Sub("mut[d1]", "mut[d2]", "❌"),
            Sub("mut[d1]", "our mut[d1]", "❌"),
            Sub("mut[d1]", "C", "❌"),
            Sub("mut[d1]", "M", "❌"),
            Sub("mut[d1.left]", "mut[d1]", "✅"),
            Sub("mut[d1.right]", "mut[d1]", "✅"),
            Sub("mut[d1.left, d1.right]", "mut[d1]", "✅"),
            Sub("mut[d1]", "mut[d1.left]", "❌"),
            Sub("mut[d1]", "mut[d1.right]", "❌"),
            Sub("mut[d1]", "mut[d1.left, d1.right]", "❌"),
            Sub("our mut[d1]", "my", "❌"),
            Sub("our mut[d1]", "our", "❌"),
            Sub("our mut[d1]", "ref[d1]", "❌"),
            Sub("our mut[d1]", "ref[d1, d2]", "❌"),
            Sub("our mut[d1]", "ref[d2]", "❌"),
            Sub("our mut[d1]", "mut[d1]", "❌"),
            Sub("our mut[d1]", "mut[d1, d2]", "❌"),
            Sub("our mut[d1]", "mut[d2]", "❌"),
            Sub("our mut[d1]", "our mut[d1]", "✅"),
            Sub("our mut[d1]", "our mut[d1, d2]", "✅"),
            Sub("our mut[d1]", "our mut[d2]", "❌"),
            Sub("our mut[d1]", "C", "❌"),
            Sub("our mut[d1]", "M", "❌"),
            Sub("C", "my", "❌"),
            Sub("C", "our", "❌"),
            Sub("C", "ref[d1]", "❌"),
            Sub("C", "mut[d1]", "❌"),
            Sub("C", "our mut[d1]", "❌"),
            Sub("C", "C", "✅"),
            Sub("C", "M", "❌"),
            Sub("M", "my", "❌"),
            Sub("M", "our", "❌"),
            Sub("M", "ref[d1]", "❌"),
            Sub("M", "mut[d1]", "❌"),
            Sub("M", "our mut[d1]", "❌"),
            Sub("M", "C", "❌"),
            Sub("M", "M", "✅"),
            With(
                "let dld1 = d1.mut;\
                 let dld2 = d2.mut;\
                 let dl1 = dld1.mut;\
                 let dl2 = dld2.mut;",
                &[
                    Sub("mut[dl1]", "mut[dl1]", "✅"),
                    Sub("mut[dl1]", "mut[dl1, dl2]", "✅"),
                    Sub("mut[dl1]", "mut[dl2]", "❌"),
                    Sub("mut[dl1]", "mut[dl1] ref[dld1]", "❌"),
                    Sub("mut[dl1]", "mut[dl1] mut[dld1]", "❌"),
                    Sub("mut[dl1]", "mut[dl1] mut[dld1, dld2]", "❌"),
                    Sub("mut[dl1]", "mut[dld1]", "✅"), // because dl1 is dead
                    Sub("mut[dl1]", "mut[dld1, dld2]", "✅"), // because dl1 is dead
                    Sub("mut[dl1]", "mut[dld2] mut[dld1]", "❌"),
                    Sub("mut[dl1]", "mut[dld2]", "❌"), // dl1 is dead but it came from dld1, not dld2
                    Sub("mut[dl1]", "mut[dl2] mut[dl2]", "❌"), // dl1 is dead but it came from dld1, not dl2
                ],
                "let _dld1 = dld1.move;\
                 let _dld2 = dld2.move;",
            ),
            With(
                "let dld1 = d1.mut;\
                 let dld2 = d2.mut;\
                 let dl1 = dld1.mut;\
                 let dl2 = dld2.mut;",
                &[
                    Sub("mut[dl1]", "mut[dl1]", "✅"),
                    Sub("mut[dl1]", "mut[dl1, dl2]", "✅"),
                    Sub("mut[dl1]", "mut[dl2]", "❌"),
                    Sub("mut[dl1]", "mut[dl1] ref[dld1]", "❌"),
                    Sub("mut[dl1]", "mut[dl1] mut[dld1]", "❌"),
                    Sub("mut[dl1]", "mut[dl1] mut[dld1, dld2]", "❌"),
                    Sub("mut[dl1]", "mut[dld1]", "❌"), // because dl1 is not dead
                    Sub("mut[dl1]", "mut[dld1, dld2]", "❌"), // because dl1 is not dead
                    Sub("mut[dl1]", "mut[dld2]", "❌"),
                    Sub("mut[dl1]", "mut[dld2] mut[dld1]", "❌"),
                    Sub("mut[dl1]", "mut[dl2] mut[dl2]", "❌"),
                ],
                "let _dl1 = dl1.move;\
                 let _dl2 = dl2.move;\
                 let _dld1 = dld1.move;\
                 let _dld2 = dld2.move;",
            ),
        ],
    );
}

#[test]
fn liskov_rules_nested() {
    run_rules_against_templates(
        D1D2_MY_DATA,
        &[With(
            "let d1l = d1.mut;\
                 let d1ll = d1l.mut;\
                 let d1lll = d1ll.mut;",
            &[
                Sub("mut[d1lll]", "mut[d1]", "✅"), // because d1lll is dead
            ],
            "",
        )],
    );
}

const MY_OUR_DATA: &str = "
    class Data {
        left: my Data;
        right: my Data;
    }
    class Main {
        fn test[perm M, perm C](
            my self,

            my_data: my Data,
            our_data: our Data,
        )
        where
            shared(C),
        {
            {PREFIX}

            let src: {SUBPERM} Data = !;
            let dst: {SUPPERM} Data = src.move;

            {SUFFIX}
        }
    }
";

#[test]
fn my_our_data() {
    run_rules_against_templates(
        MY_OUR_DATA,
        &[
            // The type `mut[our_data]` is strongly suggestive
            // that the result is actually `our` but then it would be
            // `mut[our_data] our`.
            Sub("mut[my_data]", "mut[my_data, our_data]", "✅"),
            Sub("mut[our_data]", "mut[my_data, our_data]", "✅"),
            Sub("mut[my_data, our_data]", "mut[my_data, our_data]", "✅"),
        ],
    );
}

const PAIR_LEASED: &str = "
        class Pair {
            a: my Data;
            b: my Data;
        }
        class Data { }
        class Main {
            fn test[perm P](my self, pair: P Pair) where unique(P), lent(P) {
                {PREFIX}

                let src: {SUBPERM} = !;
                let dst: {SUPPERM} = src.move;

                {SUFFIX}
            }

            fn consume_from_a[perm P](my self, pair: P Pair, from_a: mut[pair.a] Data) where unique(P), lent(P) { (); }
            fn consume_from_b[perm P](my self, pair: P Pair, from_b: mut[pair.b] Data) where unique(P), lent(P) { (); }
        }
        ";

#[test]
fn liskov_from_pair_leased_with_pair_give() {
    run_rules_against_templates(
        PAIR_LEASED,
        &[
            // In these tests, `pair` is live, and so leases from either `pair.{a,b}` cannot be canceled.
            With(
                "let d1: mut[pair.a] Data = pair.a.mut; \
                 let d2: mut[pair.b] Data = pair.b.mut;",
                &[
                    Sub("mut[d1] Data", "mut[d2] Data", "❌"),
                    Sub("mut[d1] Data", "mut[d1] Data", "✅"),
                    Sub("mut[d1] Data", "mut[d1, d2] Data", "✅"),
                    Sub("mut[d1] Data", "mut[pair.a] Data", "✅"),
                    Sub("mut[d1] Data", "mut[pair.b] Data", "❌"),
                    Sub("mut[d1] Data", "mut[pair] Data", "✅"),
                    Sub("mut[d1] Data", "mut[pair.a, pair.b] Data", "✅"),
                    Sub("mut[d2] Data", "mut[d2] Data", "✅"),
                    Sub("mut[d2] Data", "mut[d1] Data", "❌"),
                    Sub("mut[d2] Data", "mut[d1, d2] Data", "✅"),
                    Sub("mut[d2] Data", "mut[pair.a] Data", "❌"),
                    Sub("mut[d2] Data", "mut[pair.b] Data", "✅"),
                    Sub("mut[d2] Data", "mut[pair] Data", "✅"),
                    Sub("mut[d2] Data", "mut[pair.a, pair.b] Data", "✅"),
                    Sub("mut[d1, d2] Data", "mut[d2] Data", "❌"),
                    Sub("mut[d1, d2] Data", "mut[d1] Data", "❌"),
                    Sub("mut[d1, d2] Data", "mut[d1, d2] Data", "✅"),
                    Sub("mut[d1, d2] Data", "mut[d1] mut[d2] Data", "❌"),
                    Sub("mut[d1, d2] Data", "mut[pair.a] Data", "❌"),
                    Sub("mut[d1, d2] Data", "mut[pair.b] Data", "❌"),
                    Sub("mut[d1, d2] Data", "mut[pair] Data", "✅"),
                    Sub("mut[d1, d2] Data", "mut[pair.a, pair.b] Data", "✅"),
                ],
                "let _keep_pair_live = pair.move;",
            ),
        ],
    );
}

#[test]
fn liskov_from_pair_leased_with_pair_a_give() {
    run_rules_against_templates(
        PAIR_LEASED,
        &[
            // In these tests, `pair.a` is live, and so leases from `pair.a` cannot be canceled
            // (but leases from `pair.b` can be).
            With(
                "let d1: mut[pair.a] Data = pair.a.mut; \
                 let d2: mut[pair.b] Data = pair.b.mut;",
                &[
                    Sub("mut[d1] Data", "mut[d2] Data", "❌"),
                    Sub("mut[d1] Data", "mut[d1] Data", "✅"),
                    Sub("mut[d1] Data", "mut[d1, d2] Data", "✅"),
                    Sub("mut[d1] Data", "mut[pair.a] Data", "✅"),
                    Sub("mut[d1] Data", "mut[pair.b] Data", "❌"),
                    Sub("mut[d1] Data", "mut[pair] Data", "✅"),
                    Sub("mut[d1] Data", "mut[pair.a, pair.b] Data", "✅"),
                    Sub("mut[d2] Data", "mut[d2] Data", "✅"),
                    Sub("mut[d2] Data", "mut[d1] Data", "❌"),
                    Sub("mut[d2] Data", "mut[d1, d2] Data", "✅"),
                    Sub("mut[d2] Data", "mut[pair.a] Data", "❌"),
                    Sub("mut[d2] Data", "mut[pair.b] Data", "✅"),
                    Sub("mut[d2] Data", "mut[pair] Data", "✅"),
                    Sub("mut[d2] Data", "mut[pair.a, pair.b] Data", "✅"),
                    Sub("mut[d1, d2] Data", "mut[d2] Data", "❌"),
                    Sub("mut[d1, d2] Data", "mut[d1] Data", "❌"),
                    Sub("mut[d1, d2] Data", "mut[d1, d2] Data", "✅"),
                    Sub("mut[d1, d2] Data", "mut[d1] mut[d2] Data", "❌"),
                    Sub("mut[d1, d2] Data", "mut[pair.a] Data", "❌"),
                    Sub("mut[d1, d2] Data", "mut[pair.b] Data", "❌"),
                    Sub("mut[d1, d2] Data", "mut[pair] Data", "✅"),
                    Sub("mut[d1, d2] Data", "mut[pair.a, pair.b] Data", "✅"),
                ],
                "let _keep_pair_live = pair.a.move;",
            ),
        ],
    );
}

#[test]
fn liskov_from_pair_leased_with_pair_b_give() {
    run_rules_against_templates(
        PAIR_LEASED,
        &[
            // In these tests, `pair.b` is live, and so leases from `pair.b` cannot be canceled
            // (but leases from `pair.a` can be).
            With(
                "let d1: mut[pair.a] Data = pair.a.mut; \
                 let d2: mut[pair.b] Data = pair.b.mut;",
                &[
                    Sub("mut[d1] Data", "mut[d2] Data", "❌"),
                    Sub("mut[d1] Data", "mut[d1] Data", "✅"),
                    Sub("mut[d1] Data", "mut[d1, d2] Data", "✅"),
                    Sub("mut[d1] Data", "mut[pair.a] Data", "✅"),
                    Sub("mut[d1] Data", "mut[pair.b] Data", "❌"),
                    Sub("mut[d1] Data", "mut[pair] Data", "✅"),
                    Sub("mut[d1] Data", "mut[pair.a, pair.b] Data", "✅"),
                    Sub("mut[d2] Data", "mut[d2] Data", "✅"),
                    Sub("mut[d2] Data", "mut[d1] Data", "❌"),
                    Sub("mut[d2] Data", "mut[d1, d2] Data", "✅"),
                    Sub("mut[d2] Data", "mut[pair.a] Data", "❌"),
                    Sub("mut[d2] Data", "mut[pair.b] Data", "✅"),
                    Sub("mut[d2] Data", "mut[pair] Data", "✅"),
                    Sub("mut[d2] Data", "mut[pair.a, pair.b] Data", "✅"),
                    Sub("mut[d1, d2] Data", "mut[d2] Data", "❌"),
                    Sub("mut[d1, d2] Data", "mut[d1] Data", "❌"),
                    Sub("mut[d1, d2] Data", "mut[d1, d2] Data", "✅"),
                    Sub("mut[d1, d2] Data", "mut[d1] mut[d2] Data", "❌"),
                    Sub("mut[d1, d2] Data", "mut[pair.a] Data", "❌"),
                    Sub("mut[d1, d2] Data", "mut[pair.b] Data", "❌"),
                    Sub("mut[d1, d2] Data", "mut[pair] Data", "✅"),
                    Sub("mut[d1, d2] Data", "mut[pair.a, pair.b] Data", "✅"),
                ],
                "let _keep_pair_live = pair.b.move;",
            ),
        ],
    );
}

#[test]
fn liskov_from_pair_leased_with_pair_dead() {
    run_rules_against_templates(
        PAIR_LEASED,
        &[
            // In these tests, everything is dead, so `d{1,2}` can be converted to `pair.{a,b}`
            // which can be converted to `P`.
            With(
                "let d1: mut[pair.a] Data = pair.a.mut; \
                 let d2: mut[pair.b] Data = pair.b.mut;",
                &[
                    Sub("mut[d1] Data", "mut[d2] Data", "✅"), // mut[d1] = mut[pair.a] = P, same for d2
                    Sub("mut[d1] Data", "mut[d1] Data", "✅"),
                    Sub("mut[d1] Data", "mut[d1, d2] Data", "✅"),
                    Sub("mut[d1] Data", "mut[pair.a] Data", "✅"),
                    Sub("mut[d1] Data", "mut[pair.b] Data", "✅"), // mut[d1] = mut[pair.a] = P, same for d2
                    Sub("mut[d1] Data", "mut[pair] Data", "✅"),
                    Sub("mut[d1] Data", "mut[pair.a, pair.b] Data", "✅"),
                    Sub("mut[d2] Data", "mut[d2] Data", "✅"),
                    Sub("mut[d2] Data", "mut[d1] Data", "✅"),
                    Sub("mut[d2] Data", "mut[d1, d2] Data", "✅"),
                    Sub("mut[d2] Data", "mut[pair.a] Data", "✅"),
                    Sub("mut[d2] Data", "mut[pair.b] Data", "✅"),
                    Sub("mut[d2] Data", "mut[pair] Data", "✅"),
                    Sub("mut[d2] Data", "mut[pair.a, pair.b] Data", "✅"),
                    Sub("mut[d1, d2] Data", "mut[d2] Data", "✅"),
                    Sub("mut[d1, d2] Data", "mut[d1] Data", "✅"),
                    Sub("mut[d1, d2] Data", "mut[d1, d2] Data", "✅"),
                    Sub("mut[d1, d2] Data", "mut[d1] mut[d2] Data", "❌"),
                    Sub("mut[d1, d2] Data", "mut[pair.a] Data", "✅"),
                    Sub("mut[d1, d2] Data", "mut[pair.b] Data", "✅"),
                    Sub("mut[d1, d2] Data", "mut[pair] Data", "✅"),
                    Sub("mut[d1, d2] Data", "mut[pair.a, pair.b] Data", "✅"),
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

            let expected_str = "judgment `type_expr_as { expr: src . move, as_ty:";

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

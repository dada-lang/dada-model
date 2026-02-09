//! ## Liskov Substitution Principle (LSP)
//!
//! The "Liskov Substitution Principle" is that if T1 <: T2, then a value of type T1 can be
//! substituted for a value of type T2 and nothing can go wrong. My original intent for this module
//! was to systematically explore possible ways that subtyping in Dada might interfere with this
//! principle, but it turned into a set of exhaustive subtyping tests that compare various
//! combinations. I keep the name `liskov` just to honor Barbara Liskov.

use formality_core::test;
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
        left: given Data;
        right: given Data;
    }
    class Main {
        fn test[perm MY, perm OUR, perm SHARED, perm OWNED, perm UNIQUE, perm ANY](
            given self,

            d1: given Data,
            d2: given Data,
        )
        where
            unique(MY), owned(MY),
            shared(OUR), owned(OUR),
            shared(SHARED),
            unique(UNIQUE),
            owned(OWNED),
        {
            {PREFIX}

            let src: {SUBPERM} Data = !;
            let dst: {SUPPERM} Data = src.give;

            {SUFFIX}
        }
    }
";

#[test]
fn my_subtyping() {
    run_rules_against_templates(
        D1D2_MY_DATA,
        &[
            Sub("given", "given", "✅"),
            Sub("given", "shared", "❌"),
            Sub("given", "ref[d1]", "❌"),
            Sub("given", "ref[d1, d2]", "❌"),
            Sub("given", "ref[d2]", "❌"),
            Sub("given", "mut[d1]", "❌"),
            Sub("given", "mut[d1, d2]", "❌"),
            Sub("given", "mut[d2]", "❌"),
            Sub("given", "shared mut[d1]", "❌"),
            Sub("given", "MY", "✅"),
            Sub("MY", "given", "✅"),
            Sub("given", "OUR", "❌"),
            Sub("OUR", "given", "❌"),
            Sub("given", "SHARED", "❌"),
            Sub("SHARED", "given", "❌"),
            Sub("given", "UNIQUE", "❌"),
            Sub("UNIQUE", "given", "❌"),
            Sub("given", "ANY", "❌"),
            Sub("ANY", "given", "❌"),
        ],
    )
}

#[test]
fn our_subtyping() {
    run_rules_against_templates(
        D1D2_MY_DATA,
        &[
            Sub("shared", "given", "❌"),
            Sub("shared", "shared", "✅"),
            Sub("shared", "ref[d1]", "✅"),
            Sub("shared", "ref[d1, d2]", "✅"),
            Sub("shared", "ref[d2]", "✅"),
            Sub("shared", "mut[d1]", "❌"),
            Sub("shared", "mut[d1, d2]", "❌"),
            Sub("shared", "mut[d2]", "❌"),
            Sub("shared", "shared mut[d1]", "✅"),
            Sub("shared", "MY", "❌"),
            Sub("MY", "shared", "❌"),
            Sub("shared", "OUR", "✅"),
            Sub("OUR", "shared", "✅"),
            Sub("shared", "SHARED", "✅"),
            Sub("SHARED", "shared", "❌"),
            Sub("shared", "UNIQUE", "❌"),
            Sub("UNIQUE", "shared", "❌"),
            Sub("shared", "ANY", "❌"),
            Sub("ANY", "shared", "❌"),
        ],
    )
}

#[test]
fn ref_subtyping() {
    run_rules_against_templates(
        D1D2_MY_DATA,
        &[
            Sub("ref[d1]", "given", "❌"),
            Sub("ref[d1]", "shared", "❌"),
            Sub("ref[d1]", "ref[d1]", "✅"),
            Sub("ref[d1]", "ref[d1, d2]", "✅"),
            Sub("ref[d1]", "ref[d2]", "❌"),
            Sub("ref[d1]", "mut[d1]", "❌"),
            Sub("ref[d1]", "mut[d1, d2]", "❌"),
            Sub("ref[d1]", "mut[d2]", "❌"),
            Sub("ref[d1]", "shared mut[d1]", "✅"),
            Sub("ref[d1]", "MY", "❌"),
            Sub("MY", "ref[d1]", "❌"),
            Sub("ref[d1]", "OUR", "❌"),
            Sub("OUR", "ref[d1]", "✅"),
            Sub("ref[d1]", "SHARED", "❌"),
            Sub("SHARED", "ref[d1]", "❌"),
            Sub("ref[d1]", "UNIQUE", "❌"),
            Sub("UNIQUE", "ref[d1]", "❌"),
            Sub("ref[d1]", "ANY", "❌"),
            Sub("ANY", "ref[d1]", "❌"),
            Sub("ref[d1.left]", "ref[d1]", "✅"),
            Sub("ref[d1.right]", "ref[d1]", "✅"),
            Sub("ref[d1.left, d1.right]", "ref[d1]", "✅"),
            Sub("ref[d1]", "ref[d1.left]", "❌"),
            Sub("ref[d1]", "ref[d1.right]", "❌"),
            Sub("ref[d1]", "ref[d1.left, d1.right]", "❌"),
        ],
    )
}

#[test]
fn mut_subtyping() {
    run_rules_against_templates(
        D1D2_MY_DATA,
        &[
            Sub("shared mut[d1]", "given", "❌"),
            Sub("shared mut[d1]", "shared", "❌"),
            Sub("shared mut[d1]", "ref[d1]", "❌"),
            Sub("shared mut[d1]", "ref[d1, d2]", "❌"),
            Sub("shared mut[d1]", "ref[d2]", "❌"),
            Sub("shared mut[d1]", "mut[d1]", "❌"),
            Sub("shared mut[d1]", "mut[d1, d2]", "❌"),
            Sub("shared mut[d1]", "mut[d2]", "❌"),
            Sub("shared mut[d1]", "shared mut[d1]", "✅"),
            Sub("shared mut[d1]", "shared mut[d1, d2]", "✅"),
            Sub("shared mut[d1]", "shared mut[d2]", "❌"),
            Sub("shared mut[d1]", "MY", "❌"),
            Sub("MY", "shared mut[d1]", "❌"),
            Sub("shared mut[d1]", "OUR", "❌"),
            Sub("OUR", "shared mut[d1]", "✅"),
            Sub("shared mut[d1]", "SHARED", "❌"),
            Sub("SHARED", "shared mut[d1]", "❌"),
            Sub("shared mut[d1]", "UNIQUE", "❌"),
            Sub("UNIQUE", "shared mut[d1]", "❌"),
            Sub("shared mut[d1]", "ANY", "❌"),
            Sub("ANY", "shared mut[d1]", "❌"),
        ],
    )
}

#[test]
fn our_mut_subtyping() {
    run_rules_against_templates(
        D1D2_MY_DATA,
        &[
            Sub("mut[d1]", "given", "❌"),
            Sub("mut[d1]", "shared", "❌"),
            Sub("mut[d1]", "ref[d1]", "❌"),
            Sub("mut[d1]", "ref[d1, d2]", "❌"),
            Sub("mut[d1]", "ref[d2]", "❌"),
            Sub("mut[d1]", "mut[d1]", "✅"),
            Sub("mut[d1]", "mut[d1, d2]", "✅"),
            Sub("mut[d1]", "mut[d2]", "❌"),
            Sub("mut[d1]", "shared mut[d1]", "❌"),
            Sub("mut[d1]", "MY", "❌"),
            Sub("MY", "mut[d1]", "❌"),
            Sub("mut[d1]", "OUR", "❌"),
            Sub("OUR", "mut[d1]", "❌"),
            Sub("mut[d1]", "SHARED", "❌"),
            Sub("SHARED", "mut[d1]", "❌"),
            Sub("mut[d1]", "UNIQUE", "❌"),
            Sub("UNIQUE", "mut[d1]", "❌"),
            Sub("mut[d1]", "ANY", "❌"),
            Sub("ANY", "mut[d1]", "❌"),
            Sub("mut[d1.left]", "mut[d1]", "✅"),
            Sub("mut[d1.right]", "mut[d1]", "✅"),
            Sub("mut[d1.left, d1.right]", "mut[d1]", "✅"),
            Sub("mut[d1]", "mut[d1.left]", "❌"),
            Sub("mut[d1]", "mut[d1.right]", "❌"),
            Sub("mut[d1]", "mut[d1.left, d1.right]", "❌"),
        ],
    )
}

#[test]
fn variable_variable_subtyping() {
    run_rules_against_templates(
        D1D2_MY_DATA,
        &[
            Sub("MY", "MY", "✅"),
            Sub("MY", "OUR", "❌"),
            Sub("MY", "SHARED", "❌"),
            Sub("MY", "UNIQUE", "❌"),
            Sub("MY", "ANY", "❌"),
            Sub("OUR", "MY", "❌"),
            Sub("OUR", "OUR", "✅"),
            Sub("OUR", "SHARED", "✅"),
            Sub("OUR", "UNIQUE", "❌"),
            Sub("OUR", "ANY", "❌"),
            Sub("SHARED", "MY", "❌"),
            Sub("SHARED", "OUR", "❌"),
            Sub("SHARED", "SHARED", "✅"),
            Sub("SHARED", "UNIQUE", "❌"),
            Sub("SHARED", "ANY", "❌"),
            Sub("UNIQUE", "MY", "❌"),
            Sub("UNIQUE", "OUR", "❌"),
            Sub("UNIQUE", "SHARED", "❌"),
            Sub("UNIQUE", "UNIQUE", "✅"),
            Sub("UNIQUE", "ANY", "❌"),
            Sub("ANY", "MY", "❌"),
            Sub("ANY", "OUR", "❌"),
            Sub("ANY", "SHARED", "❌"),
            Sub("ANY", "UNIQUE", "❌"),
            Sub("ANY", "ANY", "✅"),
        ],
    )
}

#[test]
fn live_dead_places() {
    run_rules_against_templates(
        D1D2_MY_DATA,
        &[
            With(
                "let live1 = d1.mut;\
                 let live2 = d2.mut;\
                 let dead1 = live1.mut;\
                 let dead2 = live2.mut;",
                &[
                    Sub("mut[dead1]", "mut[dead1]", "✅"),
                    Sub("mut[dead1]", "mut[dead1, dead2]", "✅"),
                    Sub("mut[dead1]", "mut[dead2]", "❌"),
                    Sub("mut[dead1]", "mut[dead1] ref[live1]", "❌"),
                    Sub("mut[dead1]", "mut[dead1] mut[live1]", "✅"), // because dead1 is dead, lhs and rhs both become `mut[live1]`
                    Sub("mut[dead1]", "mut[dead1] mut[live1, live2]", "✅"), // because dead1 is dead, it becomes `mut[live1] <: mut[live1, live2]`, which holds
                    Sub("mut[dead1]", "mut[live1]", "✅"), // because dead1 is dead
                    Sub("mut[dead1]", "mut[live1, live2]", "✅"), // because dead1 is dead
                    Sub("mut[dead1]", "mut[live2]", "❌"), // `dead1` becomes `mut[live1]` but that is not a subperm of `mut[live2]`
                    Sub("mut[dead1]", "mut[live2] mut[live1]", "❌"), // as previous, we cannot discharge the `live1`
                    Sub("mut[dead1]", "mut[dead2] mut[live1]", "❌"), // as previous, `dead2` winds up promoted to `live2`
                    Sub("mut[dead1]", "mut[dead2] mut[dead2]", "❌"), // dead1 is dead but it came from live1, not dead2
                ],
                "let _live1 = live1.give;\
                 let _live2 = live2.give;",
            ),
            With(
                "let live1 = d1.mut;\
                 let live2 = d2.mut;\
                 let live1a = live1.mut;\
                 let live2a = live2.mut;",
                &[
                    Sub("mut[live1a]", "mut[live1a]", "✅"),
                    Sub("mut[live1a]", "mut[live1a, live2a]", "✅"),
                    Sub("mut[live1a]", "mut[live2a]", "❌"),
                    Sub("mut[live1a]", "mut[live1a] ref[live1]", "❌"),
                    Sub("mut[live1a]", "mut[live1a] mut[live1]", "✅"),
                    Sub("mut[live1a]", "mut[live1a] mut[live1, live2]", "✅"),
                    Sub("mut[live1a]", "mut[live1]", "❌"), // because live1a is not dead
                    Sub("mut[live1a]", "mut[live1, live2]", "❌"), // because live1a is not dead
                    Sub("mut[live1a]", "mut[live2]", "❌"),
                    Sub("mut[live1a]", "mut[live2] mut[live1]", "❌"),
                    Sub("mut[live1a]", "mut[live2a] mut[live2a]", "❌"),
                ],
                "let _live1a = live1a.give;\
                 let _live2a = live2a.give;\
                 let _live1 = live1.give;\
                 let _live2 = live2.give;",
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
        left: given Data;
        right: given Data;
    }
    class Main {
        fn test[perm M, perm C](
            given self,

            my_data: given Data,
            our_data: shared Data,
        )
        where
            shared(C),
        {
            {PREFIX}

            let src: {SUBPERM} Data = !;
            let dst: {SUPPERM} Data = src.give;

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
            // that the result is actually `shared` but then it would be
            // `mut[our_data] shared`.
            Sub("mut[my_data]", "mut[my_data, our_data]", "✅"),
            Sub("mut[our_data]", "mut[my_data, our_data]", "✅"),
            Sub("mut[my_data, our_data]", "mut[my_data, our_data]", "✅"),
        ],
    );
}

const PAIR_LEASED: &str = "
        class Pair {
            a: given Data;
            b: given Data;
        }
        class Data { }
        class Main {
            fn test[perm P](given self, pair: P Pair) where leased(P) {
                {PREFIX}

                let src: {SUBPERM} = !;
                let dst: {SUPPERM} = src.give;

                {SUFFIX}
            }

            fn consume_from_a[perm P](given self, pair: P Pair, from_a: mut[pair.a] Data) where leased(P) { (); }
            fn consume_from_b[perm P](given self, pair: P Pair, from_b: mut[pair.b] Data) where leased(P) { (); }
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
                "let _keep_pair_live = pair.give;",
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
                "let _keep_pair_live = pair.a.give;",
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
                "let _keep_pair_live = pair.b.give;",
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
            // which can be converted to `P`. But this doesn't let you make false assertions on
            // the supertype (e.g., `mut[d1] <: mut[d2]` does not hold because in no world did
            // the data come from d2).
            With(
                "let d1: mut[pair.a] Data = pair.a.mut; \
                 let d2: mut[pair.b] Data = pair.b.mut;",
                &[
                    Sub("mut[d1] Data", "mut[d2] Data", "❌"), // mut[d1] = mut[pair.a] = P, same for d2
                    Sub("mut[d1] Data", "mut[d1] Data", "✅"),
                    Sub("mut[d1] Data", "mut[d1, d2] Data", "✅"),
                    Sub("mut[d1] Data", "mut[pair.a] Data", "✅"),
                    Sub("mut[d1] Data", "mut[pair.b] Data", "❌"), // mut[d1] = mut[pair.a] = P, same for d2
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

            let result = crate::test_util::test_program_ok(&program);

            let expected_str = "judgment `type_expr_as { expr: src . give, as_ty:";

            match (outcome, result) {
                ("✅", result) => { let _ = result.expect("expected program to pass"); },
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

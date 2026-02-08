use crate::{dada_lang::term, type_system::check_program};
use formality_core::test;
use formality_core::test_util::ResultTestExt;

/// Check giving different messages in two fn calls works.
#[test]
#[allow(non_snake_case)]
fn send_two_different_messages() {
    check_program(&term(
        "
            class Bar {}

            class Channel[ty M] {
                fn send[perm P](P self, msg: M)
                where
                  leased(P),
                {
                }
            }

            class TheClass {
                fn empty_method(my self) {
                    let channel = new Channel[Bar]();

                    let bar1 = new Bar();
                    channel.mut.send[mut[channel]](bar1.move);

                    let bar2 = new Bar();
                    channel.mut.send[mut[channel]](bar2.move);

                    ();
                }
            }
        ",
    ))
    .assert_ok(expect_test::expect!["()"])
}

/// Check that giving same message twice in fn calls errors.
#[test]
#[allow(non_snake_case)]
fn send_same_message_twice() {
    check_program(&term(
        "
            class Bar {}

            class Channel[ty M] {
                fn send[perm P](P self, msg: M)
                where
                    leased(P),
                {
                }
            }

            class TheClass {
                fn empty_method(my self) {
                    let channel = new Channel[Bar]();
                    let bar = new Bar();
                    channel.mut.send[mut[channel]](bar.move);
                    channel.mut.send[mut[channel]](bar.move);
                    ();
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Bar { } class Channel [ty] { fn send [perm] (^perm0_0 self msg : ^ty1_0) -> () where leased(^perm0_0) { } } class TheClass { fn empty_method (my self) -> () { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . mut . send [mut [channel]] (bar . move) ; channel . mut . send [mut [channel]] (bar . move) ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . mut . send [mut [channel]] (bar . move) ; channel . mut . send [mut [channel]] (bar . move) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . mut . send [mut [channel]] (bar . move) ; channel . mut . send [mut [channel]] (bar . move) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . mut . send [mut [channel]] (bar . move) ; channel . mut . send [mut [channel]] (bar . move) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . mut . send [mut [channel]] (bar . move) ; channel . mut . send [mut [channel]] (bar . move) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let channel = new Channel [Bar] () ;, let bar = new Bar () ;, channel . mut . send [mut [channel]] (bar . move) ;, channel . mut . send [mut [channel]] (bar . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let bar = new Bar () ;, channel . mut . send [mut [channel]] (bar . move) ;, channel . mut . send [mut [channel]] (bar . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [channel . mut . send [mut [channel]] (bar . move) ;, channel . mut . send [mut [channel]] (bar . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: channel . mut . send [mut [channel]] (bar . move) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar, channel}, traversed: {} } }` failed at the following rule(s):
                                             the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: channel . mut . send [mut [channel]] (bar . move), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar, channel}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "call" failed at step #8 (src/file.rs:LL:CC) because
                                                   judgment `type_method_arguments_as { exprs: [bar . move], input_temps: [@ fresh(0)], input_names: [msg], input_tys: [Bar], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): mut [channel] Channel[Bar], bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {bar, channel}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `type_expr { expr: bar . move, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): mut [channel] Channel[Bar], bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {@ fresh(0), bar, channel}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "move place" failed at step #2 (src/file.rs:LL:CC) because
                                                           judgment `move_place { place: bar, ty: Bar, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): mut [channel] Channel[Bar], bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {@ fresh(0), bar, channel}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "copy" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `prove_is_shared { a: Bar, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): mut [channel] Channel[Bar], bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                 the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `prove_predicate { predicate: shared(Bar), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): mut [channel] Channel[Bar], bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       pattern `true` did not match value `false`
                                                             the rule "move" failed at step #0 (src/file.rs:LL:CC) because
                                                               condition evaluted to false: `!live_after.is_live(&place)`
                                                                 live_after = LivePlaces { accessed: {@ fresh(0), bar, channel}, traversed: {} }
                                                                 &place = bar"#]])
}

/// Check that calling channel with a shared(self) when leased(self) is declared errors.
#[test]
#[allow(non_snake_case)]
fn needs_leased_got_shared_self() {
    check_program(&term(
        "
            class Bar {}

            class Channel[ty M] {
                fn send[perm P](P self, msg: M)
                where
                    leased(P),
                {
                }
            }

            class TheClass {
                fn empty_method(my self) {
                    let channel = new Channel[Bar]();
                    let bar = new Bar();
                    channel.ref.send[ref[channel]](bar.move);
                    ();
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Bar { } class Channel [ty] { fn send [perm] (^perm0_0 self msg : ^ty1_0) -> () where leased(^perm0_0) { } } class TheClass { fn empty_method (my self) -> () { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . ref . send [ref [channel]] (bar . move) ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . ref . send [ref [channel]] (bar . move) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . ref . send [ref [channel]] (bar . move) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . ref . send [ref [channel]] (bar . move) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . ref . send [ref [channel]] (bar . move) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let channel = new Channel [Bar] () ;, let bar = new Bar () ;, channel . ref . send [ref [channel]] (bar . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let bar = new Bar () ;, channel . ref . send [ref [channel]] (bar . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [channel . ref . send [ref [channel]] (bar . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: channel . ref . send [ref [channel]] (bar . move) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: channel . ref . send [ref [channel]] (bar . move), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "call" failed at step #9 (src/file.rs:LL:CC) because
                                                   judgment `prove_predicates { predicate: [leased(ref [channel])], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): ref [channel] Channel[Bar], @ fresh(1): Bar, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                     the rule "prove_predicates" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_predicate { predicate: leased(ref [channel]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): ref [channel] Channel[Bar], @ fresh(1): Bar, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                         the rule "leased = unique + lent" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `prove_is_unique { a: ref [channel], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): ref [channel] Channel[Bar], @ fresh(1): Bar, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                             the rule "is-moved" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `prove_predicate { predicate: unique(ref [channel]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): ref [channel] Channel[Bar], @ fresh(1): Bar, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                   pattern `true` did not match value `false`
                                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                           pattern `true` did not match value `false`"#]])
}

/// Test where function expects a `Pair` and data borrowed from `pair`.
/// We `give` data shared from `pair.a`.
/// OK.
#[test]
#[allow(non_snake_case)]
fn take_pair_and_data__give_pair_give_data_ok() {
    check_program(&term(
        "
            class Data {}

            class Pair {
                a: Data;
                b: Data;
            }

            class TheClass {
                fn take_pair_and_data[perm P](P self, pair: my Pair, data: ref[pair] Data) {

                }

                fn empty_method(my self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.ref;
                    self.move.take_pair_and_data[my](pair.move, data.move);
                    ();
                }
            }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]])
}

/// Test where function expects a `Pair` and data borrowed from `pair`.
/// We `share` data shared from `pair.a`.
/// OK.
#[test]
#[allow(non_snake_case)]
fn take_pair_and_data__give_pair_share_data_ok() {
    check_program(&term(
        "
            class Data {}

            class Pair {
                a: Data;
                b: Data;
            }

            class TheClass {
                fn take_pair_and_data[perm P](P self, pair: my Pair, data: ref[pair] Data) {

                }

                fn empty_method(my self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.ref;
                    self.move.take_pair_and_data[my](pair.move, data.ref);
                    ();
                }
            }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]])
}

/// Test where function expects a `Pair` and data borrowed from `pair`.
/// We `share` data shared from `pair.a` but use it later.
/// Should error because `pair` has been moved.
#[test]
#[allow(non_snake_case)]
fn take_pair_and_data__give_pair_share_data_share_later() {
    check_program(&term(
        "
            class Data {}

            class Pair {
                a: Data;
                b: Data;
            }

            class TheClass {
                fn take_pair_and_data[perm P](P self, pair: my Pair, data: ref[pair] Data) {

                }

                fn empty_method(my self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.ref;
                    self.move.take_pair_and_data[my](pair.move, data.ref);
                    data.ref;
                    ();
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; } class TheClass { fn take_pair_and_data [perm] (^perm0_0 self pair : my Pair, data : ref [pair] Data) -> () { } fn empty_method (my self) -> () { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . move . take_pair_and_data [my] (pair . move, data . ref) ; data . ref ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . move . take_pair_and_data [my] (pair . move, data . ref) ; data . ref ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . move . take_pair_and_data [my] (pair . move, data . ref) ; data . ref ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . move . take_pair_and_data [my] (pair . move, data . ref) ; data . ref ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . move . take_pair_and_data [my] (pair . move, data . ref) ; data . ref ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let pair = new Pair (new Data (), new Data ()) ;, let data = pair . a . ref ;, self . move . take_pair_and_data [my] (pair . move, data . ref) ;, data . ref ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let data = pair . a . ref ;, self . move . take_pair_and_data [my] (pair . move, data . ref) ;, data . ref ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [self . move . take_pair_and_data [my] (pair . move, data . ref) ;, data . ref ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: ref [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: self . move . take_pair_and_data [my] (pair . move, data . ref) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: ref [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                             the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: self . move . take_pair_and_data [my] (pair . move, data . ref), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: ref [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "call" failed at step #10 (src/file.rs:LL:CC) because
                                                   judgment `accesses_permitted { access: drop, places: [@ fresh(2), @ fresh(1), @ fresh(0)], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): ref [data] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "accesses_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `"flat_map"` failed at the following rule(s):
                                                         failed at (src/file.rs:LL:CC) because
                                                           judgment `access_permitted { access: drop, place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): ref [data] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `env_permits_access { access: drop, place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): ref [data] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `parameters_permit_access { parameters: [ref [@ fresh(1) . a] Data], access: drop, place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): ref [data] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                     the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `parameter_permits_access { parameter: ref [@ fresh(1) . a] Data, access: drop, place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): ref [data] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                           judgment `lien_permit_access { lien: rf(@ fresh(1) . a), access: drop, accessed_place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): ref [data] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                             the rule "ref'd" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `ref_place_permits_access { shared_place: @ fresh(1) . a, access: drop, accessed_place: @ fresh(1) }` failed at the following rule(s):
                                                                                 the rule "share-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                                     &accessed_place = @ fresh(1)
                                                                                     &shared_place = @ fresh(1) . a"#]])
}

/// Test where function expects a `Pair` and data borrowed from `pair`.
/// We `give` data shared from `pair.a` but use it later.
/// Should error because `pair` has been moved.
#[test]
#[allow(non_snake_case)]
fn take_pair_and_data__give_pair_give_data_give_later() {
    check_program(&term(
        "
            class Data {}

            class Pair {
                a: Data;
                b: Data;
            }

            class TheClass {
                fn take_pair_and_data[perm P](P self, pair: my Pair, data: ref[pair] Data) {

                }

                fn empty_method(my self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.ref;
                    self.move.take_pair_and_data[my](pair.move, data.move);
                    data.move;
                    ();
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; } class TheClass { fn take_pair_and_data [perm] (^perm0_0 self pair : my Pair, data : ref [pair] Data) -> () { } fn empty_method (my self) -> () { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . move . take_pair_and_data [my] (pair . move, data . move) ; data . move ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . move . take_pair_and_data [my] (pair . move, data . move) ; data . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . move . take_pair_and_data [my] (pair . move, data . move) ; data . move ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . move . take_pair_and_data [my] (pair . move, data . move) ; data . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . move . take_pair_and_data [my] (pair . move, data . move) ; data . move ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let pair = new Pair (new Data (), new Data ()) ;, let data = pair . a . ref ;, self . move . take_pair_and_data [my] (pair . move, data . move) ;, data . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let data = pair . a . ref ;, self . move . take_pair_and_data [my] (pair . move, data . move) ;, data . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [self . move . take_pair_and_data [my] (pair . move, data . move) ;, data . move ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: ref [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: self . move . take_pair_and_data [my] (pair . move, data . move) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: ref [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                             the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: self . move . take_pair_and_data [my] (pair . move, data . move), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: ref [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "call" failed at step #10 (src/file.rs:LL:CC) because
                                                   judgment `accesses_permitted { access: drop, places: [@ fresh(2), @ fresh(1), @ fresh(0)], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): ref [@ fresh(1) . a] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "accesses_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `"flat_map"` failed at the following rule(s):
                                                         failed at (src/file.rs:LL:CC) because
                                                           judgment `access_permitted { access: drop, place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): ref [@ fresh(1) . a] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `env_permits_access { access: drop, place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): ref [@ fresh(1) . a] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                                 the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `parameters_permit_access { parameters: [ref [@ fresh(1) . a] Data], access: drop, place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): ref [@ fresh(1) . a] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                     the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `parameter_permits_access { parameter: ref [@ fresh(1) . a] Data, access: drop, place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): ref [@ fresh(1) . a] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                         the rule "parameter" failed at step #1 (src/file.rs:LL:CC) because
                                                                           judgment `lien_permit_access { lien: rf(@ fresh(1) . a), access: drop, accessed_place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): ref [@ fresh(1) . a] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                             the rule "ref'd" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `ref_place_permits_access { shared_place: @ fresh(1) . a, access: drop, accessed_place: @ fresh(1) }` failed at the following rule(s):
                                                                                 the rule "share-mutation" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                                     &accessed_place = @ fresh(1)
                                                                                     &shared_place = @ fresh(1) . a"#]])
}

/// Test where we expect data leased from self (but do nothing with it).
/// OK.
#[test]
#[allow(non_snake_case)]
fn pair_method__leased_self_ok() {
    check_program(&term(
        "
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(my self, data: mut[self] Data) {
                  ();
                }
            }

            class Main {
                fn main(my self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.mut;
                    pair.move.method(data.move);
                    ();
                }
            }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]])
}

/// Test where we expect data ref'd from self (but do nothing with it).
/// OK.
#[test]
#[allow(non_snake_case)]
fn pair_method__ref_self_ok() {
    check_program(&term(
        "
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(my self, data: ref[self] Data) {
                  ();
                }
            }

            class Main {
                fn main(my self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.ref;
                    pair.move.method(data.move);
                    ();
                }
            }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]])
}

/// Test where we expect data leased from self.a but get data from self.b.
/// Error.
#[test]
#[allow(non_snake_case)]
fn pair_method__expect_leased_self_a__got_leased_self_b() {
    check_program(&term(
        "
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(my self, data: mut[self.a] Data) {
                  ();
                }
            }

            class Main {
                fn main(my self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.b.mut;
                    pair.move.method(data.move);
                    ();
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; fn method (my self data : mut [self . a] Data) -> () { () ; } } class Main { fn main (my self) -> () { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . mut ; pair . move . method (data . move) ; () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . mut ; pair . move . method (data . move) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . mut ; pair . move . method (data . move) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . mut ; pair . move . method (data . move) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . mut ; pair . move . method (data . move) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let pair = new Pair (new Data (), new Data ()) ;, let data = pair . b . mut ;, pair . move . method (data . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let data = pair . b . mut ;, pair . move . method (data . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [pair . move . method (data . move) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: mut [pair . b] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: pair . move . method (data . move) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: mut [pair . b] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: pair . move . method (data . move), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: mut [pair . b] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "call" failed at step #8 (src/file.rs:LL:CC) because
                                                   judgment `type_method_arguments_as { exprs: [data . move], input_temps: [@ fresh(0)], input_names: [data], input_tys: [mut [@ fresh(0) . a] Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair, data: mut [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #5 (src/file.rs:LL:CC) because
                                                       judgment `sub { a: mut [@ fresh(0) . b] Data, b: mut [@ fresh(0) . a] Data, live_after: LivePlaces { accessed: {@ fresh(0)}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair, @ fresh(1): mut [@ fresh(0) . b] Data, data: mut [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                                                           judgment `sub_perms { perm_a: mut [@ fresh(0) . b], perm_b: mut [@ fresh(0) . a], live_after: LivePlaces { accessed: {@ fresh(0)}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair, @ fresh(1): mut [@ fresh(0) . b] Data, data: mut [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                             the rule "sub_red_perms" failed at step #2 (src/file.rs:LL:CC) because
                                                               judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Mtl(@ fresh(0) . b)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtl(@ fresh(0) . a)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair, @ fresh(1): mut [@ fresh(0) . b] Data, data: mut [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                                 the rule "sub_red_perms" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtl(@ fresh(0) . b)] }, red_chain_b: RedChain { links: [Mtl(@ fresh(0) . a)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair, @ fresh(1): mut [@ fresh(0) . b] Data, data: mut [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                                     the rule "(mut::P) vs (mut::P)" failed at step #0 (src/file.rs:LL:CC) because
                                                                       condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                                         place_b = @ fresh(0) . a
                                                                         &place_a = @ fresh(0) . b
                                                                     the rule "(our::P) vs (shared::P)" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `prove_is_our { a: mut [@ fresh(0) . b], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair, @ fresh(1): mut [@ fresh(0) . b] Data, data: mut [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                                         the rule "prove" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `prove_is_shared { a: mut [@ fresh(0) . b], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair, @ fresh(1): mut [@ fresh(0) . b] Data, data: mut [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                                             the rule "is" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `prove_predicate { predicate: shared(mut [@ fresh(0) . b]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair, @ fresh(1): mut [@ fresh(0) . b] Data, data: mut [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                                                 the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   pattern `true` did not match value `false`"#]])
}

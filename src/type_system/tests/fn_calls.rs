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
                    channel.lease.send[leased[channel]](bar1.give);

                    let bar2 = new Bar();
                    channel.lease.send[leased[channel]](bar2.give);

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
                    channel.lease.send[leased[channel]](bar.give);
                    channel.lease.send[leased[channel]](bar.give);
                    ();
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Bar { } class Channel [ty] { fn send [perm] (^perm0_0 self msg : ^ty1_0) -> () where leased(^perm0_0) { } } class TheClass { fn empty_method (my self) -> () { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . lease . send [leased [channel]] (bar . give) ; channel . lease . send [leased [channel]] (bar . give) ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . lease . send [leased [channel]] (bar . give) ; channel . lease . send [leased [channel]] (bar . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . lease . send [leased [channel]] (bar . give) ; channel . lease . send [leased [channel]] (bar . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . lease . send [leased [channel]] (bar . give) ; channel . lease . send [leased [channel]] (bar . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . lease . send [leased [channel]] (bar . give) ; channel . lease . send [leased [channel]] (bar . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let channel = new Channel [Bar] () ;, let bar = new Bar () ;, channel . lease . send [leased [channel]] (bar . give) ;, channel . lease . send [leased [channel]] (bar . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let bar = new Bar () ;, channel . lease . send [leased [channel]] (bar . give) ;, channel . lease . send [leased [channel]] (bar . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [channel . lease . send [leased [channel]] (bar . give) ;, channel . lease . send [leased [channel]] (bar . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: channel . lease . send [leased [channel]] (bar . give) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar, channel}, traversed: {} } }` failed at the following rule(s):
                                             the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: channel . lease . send [leased [channel]] (bar . give), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar, channel}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "call" failed at step #8 (src/file.rs:LL:CC) because
                                                   judgment `type_method_arguments_as { exprs: [bar . give], input_names: [msg], input_tys: [Bar], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): leased [channel] Channel[Bar], bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {bar, channel}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `type_expr { expr: bar . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): leased [channel] Channel[Bar], bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {bar, channel}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "give place" failed at step #2 (src/file.rs:LL:CC) because
                                                           judgment `give_place { place: bar, ty: Bar, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): leased [channel] Channel[Bar], bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {bar, channel}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "copy" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `reduces_to_copy { a: Bar, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): leased [channel] Channel[Bar], bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                 the rule "my" failed at step #1 (src/file.rs:LL:CC) because
                                                                   condition evaluted to false: `perms.is_copy(&env)`
                                                                     perms = RedPerms { copied: false, shared_from: {}, leased_from: {}, variables: {} }
                                                                     &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): leased [channel] Channel[Bar], bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 1 }
                                                             the rule "move" failed at step #0 (src/file.rs:LL:CC) because
                                                               condition evaluted to false: `!live_after.is_live(&place)`
                                                                 live_after = LivePlaces { accessed: {bar, channel}, traversed: {} }
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
                    channel.share.send[shared[channel]](bar.give);
                    ();
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Bar { } class Channel [ty] { fn send [perm] (^perm0_0 self msg : ^ty1_0) -> () where leased(^perm0_0) { } } class TheClass { fn empty_method (my self) -> () { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . share . send [shared [channel]] (bar . give) ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . share . send [shared [channel]] (bar . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . share . send [shared [channel]] (bar . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . share . send [shared [channel]] (bar . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . share . send [shared [channel]] (bar . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let channel = new Channel [Bar] () ;, let bar = new Bar () ;, channel . share . send [shared [channel]] (bar . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let bar = new Bar () ;, channel . share . send [shared [channel]] (bar . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [channel . share . send [shared [channel]] (bar . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: channel . share . send [shared [channel]] (bar . give) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: channel . share . send [shared [channel]] (bar . give), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "call" failed at step #9 (src/file.rs:LL:CC) because
                                                   judgment `prove_predicates { predicate: [leased(shared [channel])], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): shared [channel] Channel[Bar], @ fresh(1): Bar, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                     the rule "prove_predicates" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_predicate { predicate: leased(shared [channel]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): shared [channel] Channel[Bar], @ fresh(1): Bar, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                         the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `reduces_to_leased { a: shared [channel], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): shared [channel] Channel[Bar], @ fresh(1): Bar, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                             the rule "my" failed at step #1 (src/file.rs:LL:CC) because
                                                               condition evaluted to false: `perms.is_leased(&env)`
                                                                 perms = RedPerms { copied: true, shared_from: {channel}, leased_from: {}, variables: {} }
                                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): shared [channel] Channel[Bar], @ fresh(1): Bar, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 2 }"#]])
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
                fn take_pair_and_data[perm P](P self, pair: my Pair, data: shared[pair] Data) {

                }

                fn empty_method(my self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.share;
                    self.give.take_pair_and_data[my](pair.give, data.give);
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
                fn take_pair_and_data[perm P](P self, pair: my Pair, data: shared[pair] Data) {

                }

                fn empty_method(my self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.share;
                    self.give.take_pair_and_data[my](pair.give, data.share);
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
                fn take_pair_and_data[perm P](P self, pair: my Pair, data: shared[pair] Data) {

                }

                fn empty_method(my self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.share;
                    self.give.take_pair_and_data[my](pair.give, data.share);
                    data.share;
                    ();
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; } class TheClass { fn take_pair_and_data [perm] (^perm0_0 self pair : my Pair, data : shared [pair] Data) -> () { } fn empty_method (my self) -> () { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . share) ; data . share ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . share) ; data . share ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . share) ; data . share ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . share) ; data . share ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . share) ; data . share ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let pair = new Pair (new Data (), new Data ()) ;, let data = pair . a . share ;, self . give . take_pair_and_data [my] (pair . give, data . share) ;, data . share ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let data = pair . a . share ;, self . give . take_pair_and_data [my] (pair . give, data . share) ;, data . share ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [self . give . take_pair_and_data [my] (pair . give, data . share) ;, data . share ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: self . give . take_pair_and_data [my] (pair . give, data . share) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                             the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: self . give . take_pair_and_data [my] (pair . give, data . share), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "call" failed at step #8 (src/file.rs:LL:CC) because
                                                   judgment `type_method_arguments_as { exprs: [pair . give, data . share], input_names: [pair, data], input_tys: [my Pair, shared [pair] Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, data: shared [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #7 (src/file.rs:LL:CC) because
                                                       judgment `type_method_arguments_as { exprs: [data . share], input_names: [data], input_tys: [shared [@ fresh(1)] Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 2 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #5 (src/file.rs:LL:CC) because
                                                           judgment `sub { a: shared [data] shared [@ fresh(1) . a] Data, b: shared [@ fresh(1)] Data, live_after: LivePlaces { accessed: {data}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): shared [data] shared [@ fresh(1) . a] Data, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                             the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: shared [data] shared [@ fresh(1) . a] Data, chain_b: Chain { liens: [] }, b: shared [@ fresh(1)] Data, live_after: LivePlaces { accessed: {data}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): shared [data] shared [@ fresh(1) . a] Data, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                 the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                                   judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Shared(@ fresh(1) . a)] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Shared(@ fresh(1))] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {data}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): shared [data] shared [@ fresh(1) . a] Data, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                     the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Shared(@ fresh(1) . a)] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Shared(@ fresh(1))] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {data}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): shared [data] shared [@ fresh(1) . a] Data, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                         the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                                                           judgment `sub_chains { chain_a: Chain { liens: [Shared(@ fresh(1) . a)] }, chain_b: Chain { liens: [Shared(@ fresh(1))] }, live_after: LivePlaces { accessed: {data}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): shared [data] shared [@ fresh(1) . a] Data, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                             the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `chain_a.is_owned(&env)`
                                                                                 chain_a = Chain { liens: [Shared(@ fresh(1) . a)] }
                                                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): shared [data] shared [@ fresh(1) . a] Data, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }
                                                                             the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `chain_a.is_owned(&env)`
                                                                                 chain_a = Chain { liens: [Shared(@ fresh(1) . a)] }
                                                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): shared [data] shared [@ fresh(1) . a] Data, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }
                                                                             the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `chain_a.is_owned(&env)`
                                                                                 chain_a = Chain { liens: [Shared(@ fresh(1) . a)] }
                                                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): shared [data] shared [@ fresh(1) . a] Data, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }
                                                                             the rule "shared-dead" failed at step #1 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `chain_a.is_lent(&env)`
                                                                                 chain_a = Chain { liens: [] }
                                                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): shared [data] shared [@ fresh(1) . a] Data, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }
                                                                             the rule "shared-vs-shared" failed at step #2 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `place_a.is_prefix_of(&place_b)`
                                                                                 place_a = @ fresh(1) . a
                                                                                 &place_b = @ fresh(1)"#]])
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
                fn take_pair_and_data[perm P](P self, pair: my Pair, data: shared[pair] Data) {

                }

                fn empty_method(my self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.share;
                    self.give.take_pair_and_data[my](pair.give, data.give);
                    data.give;
                    ();
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; } class TheClass { fn take_pair_and_data [perm] (^perm0_0 self pair : my Pair, data : shared [pair] Data) -> () { } fn empty_method (my self) -> () { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . give) ; data . give ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . give) ; data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . give) ; data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . give) ; data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . give) ; data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let pair = new Pair (new Data (), new Data ()) ;, let data = pair . a . share ;, self . give . take_pair_and_data [my] (pair . give, data . give) ;, data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let data = pair . a . share ;, self . give . take_pair_and_data [my] (pair . give, data . give) ;, data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [self . give . take_pair_and_data [my] (pair . give, data . give) ;, data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: self . give . take_pair_and_data [my] (pair . give, data . give) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                             the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: self . give . take_pair_and_data [my] (pair . give, data . give), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "call" failed at step #8 (src/file.rs:LL:CC) because
                                                   judgment `type_method_arguments_as { exprs: [pair . give, data . give], input_names: [pair, data], input_tys: [my Pair, shared [pair] Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, data: shared [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #7 (src/file.rs:LL:CC) because
                                                       judgment `type_method_arguments_as { exprs: [data . give], input_names: [data], input_tys: [shared [@ fresh(1)] Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 2 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #5 (src/file.rs:LL:CC) because
                                                           judgment `sub { a: shared [@ fresh(1) . a] Data, b: shared [@ fresh(1)] Data, live_after: LivePlaces { accessed: {data}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): shared [@ fresh(1) . a] Data, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                             the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: shared [@ fresh(1) . a] Data, chain_b: Chain { liens: [] }, b: shared [@ fresh(1)] Data, live_after: LivePlaces { accessed: {data}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): shared [@ fresh(1) . a] Data, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                 the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                                   judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Shared(@ fresh(1) . a)] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Shared(@ fresh(1))] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {data}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): shared [@ fresh(1) . a] Data, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                     the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Shared(@ fresh(1) . a)] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Shared(@ fresh(1))] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {data}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): shared [@ fresh(1) . a] Data, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                         the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                                                           judgment `sub_chains { chain_a: Chain { liens: [Shared(@ fresh(1) . a)] }, chain_b: Chain { liens: [Shared(@ fresh(1))] }, live_after: LivePlaces { accessed: {data}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): shared [@ fresh(1) . a] Data, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                             the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `chain_a.is_owned(&env)`
                                                                                 chain_a = Chain { liens: [Shared(@ fresh(1) . a)] }
                                                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): shared [@ fresh(1) . a] Data, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }
                                                                             the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `chain_a.is_owned(&env)`
                                                                                 chain_a = Chain { liens: [Shared(@ fresh(1) . a)] }
                                                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): shared [@ fresh(1) . a] Data, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }
                                                                             the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `chain_a.is_owned(&env)`
                                                                                 chain_a = Chain { liens: [Shared(@ fresh(1) . a)] }
                                                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): shared [@ fresh(1) . a] Data, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }
                                                                             the rule "shared-dead" failed at step #1 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `chain_a.is_lent(&env)`
                                                                                 chain_a = Chain { liens: [] }
                                                                                 &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ fresh(0): my TheClass, @ fresh(1): Pair, @ fresh(2): shared [@ fresh(1) . a] Data, data: shared [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }
                                                                             the rule "shared-vs-shared" failed at step #2 (src/file.rs:LL:CC) because
                                                                               condition evaluted to false: `place_a.is_prefix_of(&place_b)`
                                                                                 place_a = @ fresh(1) . a
                                                                                 &place_b = @ fresh(1)"#]])
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

                fn method(my self, data: leased[self] Data) {
                  ();
                }
            }

            class Main {
                fn main(my self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.lease;
                    pair.give.method(data.give);
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

                fn method(my self, data: leased[self.a] Data) {
                  ();
                }
            }

            class Main {
                fn main(my self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.b.lease;
                    pair.give.method(data.give);
                    ();
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Pair { a : Data ; b : Data ; fn method (my self data : leased [self . a] Data) -> () { () ; } } class Main { fn main (my self) -> () { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . lease ; pair . give . method (data . give) ; () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . lease ; pair . give . method (data . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . lease ; pair . give . method (data . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . lease ; pair . give . method (data . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . lease ; pair . give . method (data . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let pair = new Pair (new Data (), new Data ()) ;, let data = pair . b . lease ;, pair . give . method (data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let data = pair . b . lease ;, pair . give . method (data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [pair . give . method (data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [pair . b] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: pair . give . method (data . give) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [pair . b] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                             the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: pair . give . method (data . give), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased [pair . b] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "call" failed at step #8 (src/file.rs:LL:CC) because
                                                   judgment `type_method_arguments_as { exprs: [data . give], input_names: [data], input_tys: [leased [@ fresh(0) . a] Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair, data: leased [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #5 (src/file.rs:LL:CC) because
                                                       judgment `sub { a: leased [@ fresh(0) . b] Data, b: leased [@ fresh(0) . a] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair, @ fresh(1): leased [@ fresh(0) . b] Data, data: leased [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                         the rule "sub" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `sub_under_perms { chain_a: Chain { liens: [] }, a: leased [@ fresh(0) . b] Data, chain_b: Chain { liens: [] }, b: leased [@ fresh(0) . a] Data, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair, @ fresh(1): leased [@ fresh(0) . b] Data, data: leased [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                             the rule "sub" failed at step #2 (src/file.rs:LL:CC) because
                                                               judgment `sub_some { ty_chain_a: TyChain { chain: Chain { liens: [Leased(@ fresh(0) . b)] }, ty: NamedTy(Data) }, ty_chains_b: {TyChain { chain: Chain { liens: [Leased(@ fresh(0) . a)] }, ty: NamedTy(Data) }}, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair, @ fresh(1): leased [@ fresh(0) . b] Data, data: leased [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                                 the rule "sub-some" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `sub_ty_chain { ty_chain_a: TyChain { chain: Chain { liens: [Leased(@ fresh(0) . b)] }, ty: NamedTy(Data) }, ty_chain_b: TyChain { chain: Chain { liens: [Leased(@ fresh(0) . a)] }, ty: NamedTy(Data) }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair, @ fresh(1): leased [@ fresh(0) . b] Data, data: leased [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                                     the rule "sub-named" failed at step #3 (src/file.rs:LL:CC) because
                                                                       judgment `sub_chains { chain_a: Chain { liens: [Leased(@ fresh(0) . b)] }, chain_b: Chain { liens: [Leased(@ fresh(0) . a)] }, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair, @ fresh(1): leased [@ fresh(0) . b] Data, data: leased [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                                         the rule "leased-dead" failed at step #1 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `chain_a.is_lent(&env)`
                                                                             chain_a = Chain { liens: [] }
                                                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair, @ fresh(1): leased [@ fresh(0) . b] Data, data: leased [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 }
                                                                         the rule "leased-vs-leased" failed at step #2 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `place_a.is_prefix_of(&place_b)`
                                                                             place_a = @ fresh(0) . b
                                                                             &place_b = @ fresh(0) . a
                                                                         the rule "my-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                                                             chain_a = Chain { liens: [Leased(@ fresh(0) . b)] }
                                                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair, @ fresh(1): leased [@ fresh(0) . b] Data, data: leased [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 }
                                                                         the rule "my-sub-owned" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                                                             chain_a = Chain { liens: [Leased(@ fresh(0) . b)] }
                                                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair, @ fresh(1): leased [@ fresh(0) . b] Data, data: leased [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 }
                                                                         the rule "our-sub-copy" failed at step #0 (src/file.rs:LL:CC) because
                                                                           condition evaluted to false: `chain_a.is_owned(&env)`
                                                                             chain_a = Chain { liens: [Leased(@ fresh(0) . b)] }
                                                                             &env = Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ fresh(0): Pair, @ fresh(1): leased [@ fresh(0) . b] Data, data: leased [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 }"#]])
}

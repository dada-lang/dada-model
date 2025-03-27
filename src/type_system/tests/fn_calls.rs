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
                  move(P),
                  lent(P),
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
                    move(P),
                    lent(P),
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
        check program `class Bar { } class Channel [ty] { fn send [perm] (^perm0_0 self msg : ^ty1_0) -> () where move(^perm0_0), lent(^perm0_0) { } } class TheClass { fn empty_method (my self) -> () { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . lease . send [leased [channel]] (bar . give) ; channel . lease . send [leased [channel]] (bar . give) ; () ; } }`

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
                                                 the rule "call" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: channel . lease, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar, channel}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: lease, place: channel, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar, channel}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `env_permits_access { access: lease, place: channel, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar, channel}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `parameters_permit_access { parameters: [Bar, Channel[Bar]], access: lease, place: channel, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `parameter_permits_access { parameter: Bar, access: lease, place: channel, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `liens { a: Bar, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `some_lien { a: Bar, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                               expression evaluated to an empty collection: `parameters`"#]])
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
                    move(P),
                    lent(P),
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
        check program `class Bar { } class Channel [ty] { fn send [perm] (^perm0_0 self msg : ^ty1_0) -> () where move(^perm0_0), lent(^perm0_0) { } } class TheClass { fn empty_method (my self) -> () { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . share . send [shared [channel]] (bar . give) ; () ; } }`

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
                                                 the rule "call" failed at step #1 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: channel . share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `access_permitted { access: share, place: channel, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                         the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `env_permits_access { access: share, place: channel, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar}, traversed: {} } }` failed at the following rule(s):
                                                             the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `parameters_permit_access { parameters: [Bar], access: share, place: channel, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `parameter_permits_access { parameter: Bar, access: share, place: channel, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `liens { a: Bar, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `some_lien { a: Bar, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                             the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                               expression evaluated to an empty collection: `parameters`"#]])
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
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let data = pair . a . share ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {self, data, pair}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr { expr: pair . a . share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair}, traversed: {} } }` failed at the following rule(s):
                                             the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `access_permitted { access: share, place: pair . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `env_permits_access { access: share, place: pair . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `parameters_permit_access { parameters: [my TheClass, Pair], access: share, place: pair . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `parameter_permits_access { parameter: my TheClass, access: share, place: pair . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `liens { a: my TheClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `some_lien { a: my TheClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "apply-perm-ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `some_lien { a: TheClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                           expression evaluated to an empty collection: `parameters`"#]])
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
                                     the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                       judgment `type_statement { statement: let data = pair . a . share ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {self, data, pair}, traversed: {} } }` failed at the following rule(s):
                                         the rule "let" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `type_expr { expr: pair . a . share, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair}, traversed: {} } }` failed at the following rule(s):
                                             the rule "share|lease place" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `access_permitted { access: share, place: pair . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair}, traversed: {} } }` failed at the following rule(s):
                                                 the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `env_permits_access { access: share, place: pair . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {self, pair}, traversed: {} } }` failed at the following rule(s):
                                                     the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment `parameters_permit_access { parameters: [my TheClass, Pair], access: share, place: pair . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `parameter_permits_access { parameter: my TheClass, access: share, place: pair . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                             the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `liens { a: my TheClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                 the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                                                   judgment `some_lien { a: my TheClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                     the rule "apply-perm-ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `some_lien { a: TheClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                                         the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                                           expression evaluated to an empty collection: `parameters`"#]])
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
            0: check class named `Pair`
            1: check method named `method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: leased [self . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: leased [self . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: leased [self . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: leased [self . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [() ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: leased [self . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: leased [self . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "expr" failed at step #3 (src/file.rs:LL:CC) because
                                       judgment `parameter_permits_access { parameter: (), access: drop, place: @ fresh(0), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, @ fresh(0): (), data: leased [self . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                         the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                           judgment `liens { a: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, @ fresh(0): (), data: leased [self . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                             the rule "my" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `some_lien { a: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, @ fresh(0): (), data: leased [self . a] Data}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                 the rule "named" failed at step #0 (src/file.rs:LL:CC) because
                                                   expression evaluated to an empty collection: `parameters`"#]])
}

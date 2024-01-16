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
                    channel.lease.send[leased(channel)](bar1.give);

                    let bar2 = new Bar();
                    channel.lease.send[leased(channel)](bar2.give);

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
                    channel.lease.send[leased(channel)](bar.give);
                    channel.lease.send[leased(channel)](bar.give);
                    ();
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Bar { } class Channel [ty] { fn send [perm] (^perm0_0 self msg : ^ty1_0) -> () where leased(^perm0_0) { } } class TheClass { fn empty_method (my self) -> () { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . lease . send [leased (channel)] (bar . give) ; channel . lease . send [leased (channel)] (bar . give) ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . lease . send [leased (channel)] (bar . give) ; channel . lease . send [leased (channel)] (bar . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . lease . send [leased (channel)] (bar . give) ; channel . lease . send [leased (channel)] (bar . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . lease . send [leased (channel)] (bar . give) ; channel . lease . send [leased (channel)] (bar . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . lease . send [leased (channel)] (bar . give) ; channel . lease . send [leased (channel)] (bar . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let channel = new Channel [Bar] () ;, let bar = new Bar () ;, channel . lease . send [leased (channel)] (bar . give) ;, channel . lease . send [leased (channel)] (bar . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let bar = new Bar () ;, channel . lease . send [leased (channel)] (bar . give) ;, channel . lease . send [leased (channel)] (bar . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, channel: Channel[Bar]}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [channel . lease . send [leased (channel)] (bar . give) ;, channel . lease . send [leased (channel)] (bar . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                           judgment `type_statements_with_final_ty { statements: [channel . lease . send [leased (channel)] (bar . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                             the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                               judgment `type_statement { statement: channel . lease . send [leased (channel)] (bar . give) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                 the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `type_expr { expr: channel . lease . send [leased (channel)] (bar . give), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                     the rule "call" failed at step #9 (src/file.rs:LL:CC) because
                                                       judgment `type_method_arguments_as { exprs: [bar . give], input_names: [msg], input_temps: [@ temp(1)], input_tys: [Bar], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): leased (channel) Channel[Bar], bar: Bar, channel: Channel[Bar]}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `type_expr { expr: bar . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): leased (channel) Channel[Bar], bar: Bar, channel: Channel[Bar]}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                             the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `access_permitted { access: give, place: bar, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): leased (channel) Channel[Bar], bar: Bar, channel: Channel[Bar]}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                                 the rule "access_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                                   condition evaluted to false: `!flow.is_moved(&place)`
                                                                     flow = Flow { moved_places: {bar} }
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
                    channel.share.send[shared(channel)](bar.give);
                    ();
                }
            }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Bar { } class Channel [ty] { fn send [perm] (^perm0_0 self msg : ^ty1_0) -> () where leased(^perm0_0) { } } class TheClass { fn empty_method (my self) -> () { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . share . send [shared (channel)] (bar . give) ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . share . send [shared (channel)] (bar . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . share . send [shared (channel)] (bar . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . share . send [shared (channel)] (bar . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . share . send [shared (channel)] (bar . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let channel = new Channel [Bar] () ;, let bar = new Bar () ;, channel . share . send [shared (channel)] (bar . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let bar = new Bar () ;, channel . share . send [shared (channel)] (bar . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, channel: Channel[Bar]}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [channel . share . send [shared (channel)] (bar . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: channel . share . send [shared (channel)] (bar . give) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                             the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: channel . share . send [shared (channel)] (bar . give), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                 the rule "call" failed at step #10 (src/file.rs:LL:CC) because
                                                   judgment `prove_predicates { predicate: [leased(shared (channel))], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): shared (channel) Channel[Bar], @ temp(1): Bar, bar: Bar, channel: Channel[Bar]}, existentials: [], assumptions: {} } }` failed at the following rule(s):
                                                     the rule "prove_predicates" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_predicate { predicate: leased(shared (channel)), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): shared (channel) Channel[Bar], @ temp(1): Bar, bar: Bar, channel: Channel[Bar]}, existentials: [], assumptions: {} } }` failed at the following rule(s):
                                                         the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment had no applicable rules: `is_leased { a: shared (channel), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): shared (channel) Channel[Bar], @ temp(1): Bar, bar: Bar, channel: Channel[Bar]}, existentials: [], assumptions: {} } }`"#]])
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
                fn take_pair_and_data[perm P](P self, pair: my Pair, data: shared(pair) Data) {

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
                fn take_pair_and_data[perm P](P self, pair: my Pair, data: shared(pair) Data) {

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
///
/// FIXME: This test fails at the wrong point, it fails when we evaluate
/// data.give because `@temp` etc are not in the environment. We can probably
/// crate a test taht should pass but fails for this same reason.
/// It SHOULD Be failing when we evaluate to drop later on.
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
                fn take_pair_and_data[perm P](P self, pair: my Pair, data: shared(pair) Data) {

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
        check program `class Data { } class Pair { a : Data ; b : Data ; } class TheClass { fn take_pair_and_data [perm] (^perm0_0 self pair : my Pair, data : shared (pair) Data) -> () { } fn empty_method (my self) -> () { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . share) ; data . share ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . share) ; data . share ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . share) ; data . share ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . share) ; data . share ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . share) ; data . share ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let pair = new Pair (new Data (), new Data ()) ;, let data = pair . a . share ;, self . give . take_pair_and_data [my] (pair . give, data . share) ;, data . share ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let data = pair . a . share ;, self . give . take_pair_and_data [my] (pair . give, data . share) ;, data . share ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [self . give . take_pair_and_data [my] (pair . give, data . share) ;, data . share ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared (pair . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: self . give . take_pair_and_data [my] (pair . give, data . share) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared (pair . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {data} } }` failed at the following rule(s):
                                             the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: self . give . take_pair_and_data [my] (pair . give, data . share), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared (pair . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {data} } }` failed at the following rule(s):
                                                 the rule "call" failed at step #11 (src/file.rs:LL:CC) because
                                                   judgment `accesses_permitted { access: drop, places: [@ temp(0), @ temp(1), @ temp(2)], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (data) shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} }, live_after: LiveVars { vars: {data} } }` failed at the following rule(s):
                                                     the rule "accesses_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `"flat_map"` failed at the following rule(s):
                                                         failed at (src/file.rs:LL:CC) because
                                                           judgment `access_permitted { access: drop, place: @ temp(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (data) shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} }, live_after: LiveVars { vars: {data} } }` failed at the following rule(s):
                                                             the rule "access_permitted" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `env_permits_access { access: drop, place: @ temp(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (data) shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} }, live_after: LiveVars { vars: {data} } }` failed at the following rule(s):
                                                                 the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `parameters_permit_access { parameters: [shared (@ temp(1) . a) Data], access: drop, place: @ temp(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (data) shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} } }` failed at the following rule(s):
                                                                     the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `parameter_permits_access { parameter: shared (@ temp(1) . a) Data, access: drop, place: @ temp(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (data) shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} } }` failed at the following rule(s):
                                                                         the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `ty_permits_access { ty: shared (@ temp(1) . a) Data, access: drop, place: @ temp(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (data) shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} } }` failed at the following rule(s):
                                                                             the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `perm_permits_access { perm: shared (@ temp(1) . a), access: drop, place: @ temp(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (data) shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} } }` failed at the following rule(s):
                                                                                 the rule "disjoint" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   condition evaluted to false: `place_disjoint_from_all_of(&accessed_place, &perm_places)`
                                                                                     &accessed_place = @ temp(1)
                                                                                     &perm_places = {@ temp(1) . a}"#]])
}

/// Test where function expects a `Pair` and data borrowed from `pair`.
/// We `give` data shared from `pair.a` but use it later.
/// Should error because `pair` has been moved.
///
/// FIXME: This test fails at the wrong point, it fails when we evaluate
/// data.give because `@temp` etc are not in the environment. We can probably
/// crate a test taht should pass but fails for this same reason.
/// It SHOULD Be failing when we evaluate to drop later on.
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
                fn take_pair_and_data[perm P](P self, pair: my Pair, data: shared(pair) Data) {

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
        check program `class Data { } class Pair { a : Data ; b : Data ; } class TheClass { fn take_pair_and_data [perm] (^perm0_0 self pair : my Pair, data : shared (pair) Data) -> () { } fn empty_method (my self) -> () { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . give) ; data . give ; () ; } }`

        Caused by:
            0: check class named `TheClass`
            1: check method named `empty_method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . give) ; data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . give) ; data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . give) ; data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . share ; self . give . take_pair_and_data [my] (pair . give, data . give) ; data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let pair = new Pair (new Data (), new Data ()) ;, let data = pair . a . share ;, self . give . take_pair_and_data [my] (pair . give, data . give) ;, data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let data = pair . a . share ;, self . give . take_pair_and_data [my] (pair . give, data . give) ;, data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [self . give . take_pair_and_data [my] (pair . give, data . give) ;, data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared (pair . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: self . give . take_pair_and_data [my] (pair . give, data . give) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared (pair . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {data} } }` failed at the following rule(s):
                                             the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: self . give . take_pair_and_data [my] (pair . give, data . give), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared (pair . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {data} } }` failed at the following rule(s):
                                                 the rule "call" failed at step #11 (src/file.rs:LL:CC) because
                                                   judgment `accesses_permitted { access: drop, places: [@ temp(0), @ temp(1), @ temp(2)], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, data, pair} }, live_after: LiveVars { vars: {data} } }` failed at the following rule(s):
                                                     the rule "accesses_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `"flat_map"` failed at the following rule(s):
                                                         failed at (src/file.rs:LL:CC) because
                                                           judgment `access_permitted { access: drop, place: @ temp(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, data, pair} }, live_after: LiveVars { vars: {data} } }` failed at the following rule(s):
                                                             the rule "access_permitted" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `env_permits_access { access: drop, place: @ temp(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, data, pair} }, live_after: LiveVars { vars: {data} } }` failed at the following rule(s):
                                                                 the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `parameters_permit_access { parameters: [shared (@ temp(1) . a) Data], access: drop, place: @ temp(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, data, pair} } }` failed at the following rule(s):
                                                                     the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `parameter_permits_access { parameter: shared (@ temp(1) . a) Data, access: drop, place: @ temp(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, data, pair} } }` failed at the following rule(s):
                                                                         the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `ty_permits_access { ty: shared (@ temp(1) . a) Data, access: drop, place: @ temp(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, data, pair} } }` failed at the following rule(s):
                                                                             the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `perm_permits_access { perm: shared (@ temp(1) . a), access: drop, place: @ temp(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, data, pair} } }` failed at the following rule(s):
                                                                                 the rule "disjoint" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   condition evaluted to false: `place_disjoint_from_all_of(&accessed_place, &perm_places)`
                                                                                     &accessed_place = @ temp(1)
                                                                                     &perm_places = {@ temp(1) . a}
                                                 the rule "call" failed at step #11 (src/file.rs:LL:CC) because
                                                   judgment `accesses_permitted { access: drop, places: [@ temp(0), @ temp(1), @ temp(2)], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} }, live_after: LiveVars { vars: {data} } }` failed at the following rule(s):
                                                     the rule "accesses_permitted" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `"flat_map"` failed at the following rule(s):
                                                         failed at (src/file.rs:LL:CC) because
                                                           judgment `access_permitted { access: drop, place: @ temp(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} }, live_after: LiveVars { vars: {data} } }` failed at the following rule(s):
                                                             the rule "access_permitted" failed at step #1 (src/file.rs:LL:CC) because
                                                               judgment `env_permits_access { access: drop, place: @ temp(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} }, live_after: LiveVars { vars: {data} } }` failed at the following rule(s):
                                                                 the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `parameters_permit_access { parameters: [shared (@ temp(1) . a) Data], access: drop, place: @ temp(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} } }` failed at the following rule(s):
                                                                     the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                       judgment `parameter_permits_access { parameter: shared (@ temp(1) . a) Data, access: drop, place: @ temp(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} } }` failed at the following rule(s):
                                                                         the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `ty_permits_access { ty: shared (@ temp(1) . a) Data, access: drop, place: @ temp(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} } }` failed at the following rule(s):
                                                                             the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `perm_permits_access { perm: shared (@ temp(1) . a), access: drop, place: @ temp(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, @ temp(0): my TheClass, @ temp(1): Pair, @ temp(2): shared (@ temp(1) . a) Data, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} } }` failed at the following rule(s):
                                                                                 the rule "disjoint" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   condition evaluted to false: `place_disjoint_from_all_of(&accessed_place, &perm_places)`
                                                                                     &accessed_place = @ temp(1)
                                                                                     &perm_places = {@ temp(1) . a}"#]])
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

                fn method(my self, data: leased(self) Data) {
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

                fn method(my self, data: leased(self.a) Data) {
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
        check program `class Data { } class Pair { a : Data ; b : Data ; fn method (my self data : leased (self . a) Data) -> () { () ; } } class Main { fn main (my self) -> () { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . lease ; pair . give . method (data . give) ; () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `main`
            2: check function body
            3: judgment `can_type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . lease ; pair . give . method (data . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . lease ; pair . give . method (data . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . lease ; pair . give . method (data . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . lease ; pair . give . method (data . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [let pair = new Pair (new Data (), new Data ()) ;, let data = pair . b . lease ;, pair . give . method (data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                   judgment `type_statements_with_final_ty { statements: [let data = pair . b . lease ;, pair . give . method (data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                     the rule "cons" failed at step #2 (src/file.rs:LL:CC) because
                                       judgment `type_statements_with_final_ty { statements: [pair . give . method (data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased (pair . b) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                         the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                           judgment `type_statement { statement: pair . give . method (data . give) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased (pair . b) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                             the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `type_expr { expr: pair . give . method (data . give), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, data: leased (pair . b) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                 the rule "call" failed at step #9 (src/file.rs:LL:CC) because
                                                   judgment `type_method_arguments_as { exprs: [data . give], input_names: [data], input_temps: [@ temp(1)], input_tys: [leased (@ temp(0) . a) Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ temp(0): Pair, data: leased (@ temp(0) . b) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {pair} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #5 (src/file.rs:LL:CC) because
                                                       judgment `sub { a: leased (@ temp(0) . b) Data, b: leased (@ temp(0) . a) Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ temp(0): Pair, @ temp(1): leased (@ temp(0) . b) Data, data: leased (@ temp(0) . b) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {data, pair} } }` failed at the following rule(s):
                                                         the rule "apply-perms" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `sub { a: leased (@ temp(0) . b), b: leased (@ temp(0) . a), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, @ temp(0): Pair, @ temp(1): leased (@ temp(0) . b) Data, data: leased (@ temp(0) . b) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {data, pair} } }` failed at the following rule(s):
                                                             the rule "leased perms" failed at step #0 (src/file.rs:LL:CC) because
                                                               condition evaluted to false: `all_places_covered_by_one_of(&places_a, &places_b)`
                                                                 &places_a = {@ temp(0) . b}
                                                                 &places_b = {@ temp(0) . a}"#]])
}

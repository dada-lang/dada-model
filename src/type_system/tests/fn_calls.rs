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
                                                     the rule "call" failed at step #7 (src/file.rs:LL:CC) because
                                                       judgment `type_method_arguments_as { exprs: [bar . give], input_temps: [@ temp(1)], input_tys: [Bar], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `type_expr { expr: bar . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
                                                             the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `access_permitted { access: give, place: bar, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {bar} }, live_after: LiveVars { vars: {} } }` failed at the following rule(s):
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
                                                 the rule "call" failed at step #9 (src/file.rs:LL:CC) because
                                                   judgment `prove_predicates { predicate: [leased(shared (channel))], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, existentials: [], assumptions: {} } }` failed at the following rule(s):
                                                     the rule "prove_predicates" failed at step #0 (src/file.rs:LL:CC) because
                                                       judgment `prove_predicate { predicate: leased(shared (channel)), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, existentials: [], assumptions: {} } }` failed at the following rule(s):
                                                         the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment had no applicable rules: `is_leased { a: shared (channel), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, bar: Bar, channel: Channel[Bar]}, existentials: [], assumptions: {} } }`"#]])
}

/// Test where function expects a `Pair` and data borrowed from `pair`.
/// We `give` data shared from `pair.a`.
/// OK.
#[test]
#[allow(non_snake_case)]
fn take_pair_and_data__give_a_ok() {
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
fn take_pair_and_data__share_a_ok() {
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
/// We `give` data shared from `pair.a` but use it later.
/// Should error because `pair` has been moved.
///
/// FIXME: This test fails at the wrong point, it fails when we evaluate
/// data.give because `@temp` etc are not in the environment. We can probably
/// crate a test taht should pass but fails for this same reason.
/// It SHOULD Be failing when we evaluate to drop later on.
#[test]
#[allow(non_snake_case)]
fn take_pair_and_data__give_a_invalidates_data() {
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
                                                 the rule "call" failed at step #7 (src/file.rs:LL:CC) because
                                                   judgment `type_method_arguments_as { exprs: [pair . give, data . give], input_temps: [@ temp(1), @ temp(2)], input_tys: [my Pair, shared (@ temp(1)) Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared (pair . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self} }, live_after: LiveVars { vars: {data} } }` failed at the following rule(s):
                                                     the rule "cons" failed at step #4 (src/file.rs:LL:CC) because
                                                       judgment `type_method_arguments_as { exprs: [data . give], input_temps: [@ temp(2)], input_tys: [shared (@ temp(1)) Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} }, live_after: LiveVars { vars: {data} } }` failed at the following rule(s):
                                                         the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                           judgment `type_expr { expr: data . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} }, live_after: LiveVars { vars: {data} } }` failed at the following rule(s):
                                                             the rule "give place" failed at step #0 (src/file.rs:LL:CC) because
                                                               judgment `access_permitted { access: give, place: data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} }, live_after: LiveVars { vars: {data} } }` failed at the following rule(s):
                                                                 the rule "access_permitted" failed at step #1 (src/file.rs:LL:CC) because
                                                                   judgment `env_permits_access { access: give, place: data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} }, live_after: LiveVars { vars: {data} } }` failed at the following rule(s):
                                                                     the rule "env_permits_access" failed at step #1 (src/file.rs:LL:CC) because
                                                                       judgment `parameters_permit_access { parameters: [shared (@ temp(1) . a) Data], access: give, place: data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} } }` failed at the following rule(s):
                                                                         the rule "cons" failed at step #0 (src/file.rs:LL:CC) because
                                                                           judgment `parameter_permits_access { parameter: shared (@ temp(1) . a) Data, access: give, place: data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} } }` failed at the following rule(s):
                                                                             the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                               judgment `ty_permits_access { ty: shared (@ temp(1) . a) Data, access: give, place: data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} } }` failed at the following rule(s):
                                                                                 the rule "ty" failed at step #0 (src/file.rs:LL:CC) because
                                                                                   judgment `perm_permits_access { perm: shared (@ temp(1) . a), access: give, place: data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} } }` failed at the following rule(s):
                                                                                     the rule "disjoint" failed at step #1 (src/file.rs:LL:CC) because
                                                                                       judgment `perm_places_permit_access { perm_places: {@ temp(1) . a}, access: give, place: data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} } }` failed at the following rule(s):
                                                                                         the rule "nil" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `place_ty { place: @ temp(1) . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} } }` failed at the following rule(s):
                                                                                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               no variable named `@ temp(1)`
                                                                                     the rule "disjoint-or-prefix" failed at step #1 (src/file.rs:LL:CC) because
                                                                                       judgment `perm_places_permit_access { perm_places: {@ temp(1) . a}, access: give, place: data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} }, flow: Flow { moved_places: {self, pair} } }` failed at the following rule(s):
                                                                                         the rule "nil" failed at step #0 (src/file.rs:LL:CC) because
                                                                                           judgment `place_ty { place: @ temp(1) . a, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my TheClass, data: shared (@ temp(1) . a) Data, pair: Pair}, existentials: [], assumptions: {} } }` failed at the following rule(s):
                                                                                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                                                                                               no variable named `@ temp(1)`"#]])
}

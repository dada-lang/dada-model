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
                  unique(P),
                  lent(P),
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
                    unique(P),
                    lent(P),
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
        check program `class Bar { } class Channel [ty] { fn send [perm] (^perm0_0 self msg : ^ty1_0) -> () where unique(^perm0_0), lent(^perm0_0) { } } class TheClass { fn empty_method (my self) -> () { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . mut . send [mut [channel]] (bar . move) ; channel . mut . send [mut [channel]] (bar . move) ; () ; } }`

        Caused by:
            0: check class named `Channel`
            1: check method named `send`
            2: check function body
            3: judgment `can_type_expr_as { expr: { }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!ty_0, !perm_1], local_variables: {self: !perm_1 Channel[!ty_0], msg: !ty_0}, assumptions: {unique(!perm_1), lent(!perm_1), relative(!perm_1), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!ty_0, !perm_1], local_variables: {self: !perm_1 Channel[!ty_0], msg: !ty_0}, assumptions: {unique(!perm_1), lent(!perm_1), relative(!perm_1), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: (), b: (), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!ty_0, !perm_1], local_variables: {self: !perm_1 Channel[!ty_0], msg: !ty_0}, assumptions: {unique(!perm_1), lent(!perm_1), relative(!perm_1), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                           judgment `sub_perms { a: my, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!ty_0, !perm_1], local_variables: {self: !perm_1 Channel[!ty_0], msg: !ty_0}, assumptions: {unique(!perm_1), lent(!perm_1), relative(!perm_1), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "apply to shared" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(2), in_scope_vars: [!ty_0, !perm_1], local_variables: {self: !perm_1 Channel[!ty_0], msg: !ty_0}, assumptions: {unique(!perm_1), lent(!perm_1), relative(!perm_1), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(2), in_scope_vars: [!ty_0, !perm_1], local_variables: {self: !perm_1 Channel[!ty_0], msg: !ty_0}, assumptions: {unique(!perm_1), lent(!perm_1), relative(!perm_1), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                       pattern `true` did not match value `false`"#]])
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
                    unique(P),
                    lent(P),
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
        check program `class Bar { } class Channel [ty] { fn send [perm] (^perm0_0 self msg : ^ty1_0) -> () where unique(^perm0_0), lent(^perm0_0) { } } class TheClass { fn empty_method (my self) -> () { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . ref . send [ref [channel]] (bar . move) ; () ; } }`

        Caused by:
            0: check class named `Channel`
            1: check method named `send`
            2: check function body
            3: judgment `can_type_expr_as { expr: { }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!ty_0, !perm_1], local_variables: {self: !perm_1 Channel[!ty_0], msg: !ty_0}, assumptions: {unique(!perm_1), lent(!perm_1), relative(!perm_1), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { }, as_ty: (), env: Env { program: "...", universe: universe(2), in_scope_vars: [!ty_0, !perm_1], local_variables: {self: !perm_1 Channel[!ty_0], msg: !ty_0}, assumptions: {unique(!perm_1), lent(!perm_1), relative(!perm_1), atomic(!perm_1)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: (), b: (), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!ty_0, !perm_1], local_variables: {self: !perm_1 Channel[!ty_0], msg: !ty_0}, assumptions: {unique(!perm_1), lent(!perm_1), relative(!perm_1), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                           judgment `sub_perms { a: my, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(2), in_scope_vars: [!ty_0, !perm_1], local_variables: {self: !perm_1 Channel[!ty_0], msg: !ty_0}, assumptions: {unique(!perm_1), lent(!perm_1), relative(!perm_1), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "apply to shared" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(2), in_scope_vars: [!ty_0, !perm_1], local_variables: {self: !perm_1 Channel[!ty_0], msg: !ty_0}, assumptions: {unique(!perm_1), lent(!perm_1), relative(!perm_1), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(2), in_scope_vars: [!ty_0, !perm_1], local_variables: {self: !perm_1 Channel[!ty_0], msg: !ty_0}, assumptions: {unique(!perm_1), lent(!perm_1), relative(!perm_1), atomic(!perm_1)}, fresh: 0 } }` failed at the following rule(s):
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
            1: check method named `take_pair_and_data`
            2: check function body
            3: judgment `can_type_expr_as { expr: { }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 TheClass, data: ref [pair] Data, pair: my Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 TheClass, data: ref [pair] Data, pair: my Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: (), b: (), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 TheClass, data: ref [pair] Data, pair: my Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                           judgment `sub_perms { a: my, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 TheClass, data: ref [pair] Data, pair: my Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "apply to shared" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 TheClass, data: ref [pair] Data, pair: my Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 TheClass, data: ref [pair] Data, pair: my Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                       pattern `true` did not match value `false`"#]])
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
            1: check method named `take_pair_and_data`
            2: check function body
            3: judgment `can_type_expr_as { expr: { }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 TheClass, data: ref [pair] Data, pair: my Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { }, as_ty: (), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 TheClass, data: ref [pair] Data, pair: my Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: (), b: (), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 TheClass, data: ref [pair] Data, pair: my Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                           judgment `sub_perms { a: my, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 TheClass, data: ref [pair] Data, pair: my Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                             the rule "apply to shared" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 TheClass, data: ref [pair] Data, pair: my Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(1), in_scope_vars: [!perm_0], local_variables: {self: !perm_0 TheClass, data: ref [pair] Data, pair: my Pair}, assumptions: {relative(!perm_0), atomic(!perm_0)}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                       pattern `true` did not match value `false`"#]])
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
            0: check class named `Pair`
            1: check method named `method`
            2: check function body
            3: judgment `can_type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: mut [self . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: mut [self . a] Data}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #1 (src/file.rs:LL:CC) because
                       judgment `sub { a: (), b: (), live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: mut [self . a] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "sub-classes" failed at step #3 (src/file.rs:LL:CC) because
                           judgment `sub_perms { a: my, b: my, live_after: LivePlaces { accessed: {}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: mut [self . a] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "apply to shared" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `prove_is_shared { a: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: mut [self . a] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                 the rule "is-copy" failed at step #0 (src/file.rs:LL:CC) because
                                   judgment `prove_predicate { predicate: shared(my), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Pair, data: mut [self . a] Data}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                     the rule "parameter" failed at step #0 (src/file.rs:LL:CC) because
                                       pattern `true` did not match value `false`"#]])
}

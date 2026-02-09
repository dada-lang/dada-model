use formality_core::test;

/// Check giving different messages in two fn calls works.
#[test]
#[allow(non_snake_case)]
fn send_two_different_messages() {
    crate::assert_ok!("
            class Bar {}

            class Channel[ty M] {
                fn send[perm P](P self, msg: M)
                where
                  mut(P),
                {
                }
            }

            class TheClass {
                fn empty_method(given self) {
                    let channel = new Channel[Bar]();

                    let bar1 = new Bar();
                    channel.mut.send[mut[channel]](bar1.give);

                    let bar2 = new Bar();
                    channel.mut.send[mut[channel]](bar2.give);

                    ();
                }
            }
        ")
}

/// Check that giving same message twice in fn calls errors.
#[test]
#[allow(non_snake_case)]
fn send_same_message_twice() {
    crate::assert_err!("
            class Bar {}

            class Channel[ty M] {
                fn send[perm P](P self, msg: M)
                where
                    mut(P),
                {
                }
            }

            class TheClass {
                fn empty_method(given self) {
                    let channel = new Channel[Bar]();
                    let bar = new Bar();
                    channel.mut.send[mut[channel]](bar.give);
                    channel.mut.send[mut[channel]](bar.give);
                    ();
                }
            }
        ", expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "give" at (expressions.rs) failed because
              condition evaluted to false: `!live_after.is_live(&place)`
                live_after = LivePlaces { accessed: {@ fresh(0), bar, channel}, traversed: {} }
                &place = bar"#]])
}

/// Check that calling channel with a copy(self) when mut(self) is declared errors.
#[test]
#[allow(non_snake_case)]
fn needs_leased_got_shared_self() {
    crate::assert_err!("
            class Bar {}

            class Channel[ty M] {
                fn send[perm P](P self, msg: M)
                where
                    mut(P),
                {
                }
            }

            class TheClass {
                fn empty_method(given self) {
                    let channel = new Channel[Bar]();
                    let bar = new Bar();
                    channel.ref.send[ref[channel]](bar.give);
                    ();
                }
            }
        ", expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]])
}

/// Test where function expects a `Pair` and data borrowed from `pair`.
/// We `give` data shared from `pair.a`.
/// OK.
#[test]
#[allow(non_snake_case)]
fn take_pair_and_data__give_pair_give_data_ok() {
    crate::assert_ok!("
            class Data {}

            class Pair {
                a: Data;
                b: Data;
            }

            class TheClass {
                fn take_pair_and_data[perm P](P self, pair: given Pair, data: ref[pair] Data) {

                }

                fn empty_method(given self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.ref;
                    self.give.take_pair_and_data[given](pair.give, data.give);
                    ();
                }
            }
        ")
}

/// Test where function expects a `Pair` and data borrowed from `pair`.
/// We `share` data shared from `pair.a`.
/// OK.
#[test]
#[allow(non_snake_case)]
fn take_pair_and_data__give_pair_share_data_ok() {
    crate::assert_ok!("
            class Data {}

            class Pair {
                a: Data;
                b: Data;
            }

            class TheClass {
                fn take_pair_and_data[perm P](P self, pair: given Pair, data: ref[pair] Data) {

                }

                fn empty_method(given self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.ref;
                    self.give.take_pair_and_data[given](pair.give, data.ref);
                    ();
                }
            }
        ")
}

/// Test where function expects a `Pair` and data borrowed from `pair`.
/// We `share` data shared from `pair.a` but use it later.
/// Should error because `pair` has been moved.
#[test]
#[allow(non_snake_case)]
fn take_pair_and_data__give_pair_share_data_share_later() {
    crate::assert_err!("
            class Data {}

            class Pair {
                a: Data;
                b: Data;
            }

            class TheClass {
                fn take_pair_and_data[perm P](P self, pair: given Pair, data: ref[pair] Data) {

                }

                fn empty_method(given self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.ref;
                    self.give.take_pair_and_data[given](pair.give, data.ref);
                    data.ref;
                    ();
                }
            }
        ", expect_test::expect![[r#"
            the rule "share-mutation" at (accesses.rs) failed because
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
    crate::assert_err!("
            class Data {}

            class Pair {
                a: Data;
                b: Data;
            }

            class TheClass {
                fn take_pair_and_data[perm P](P self, pair: given Pair, data: ref[pair] Data) {

                }

                fn empty_method(given self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.ref;
                    self.give.take_pair_and_data[given](pair.give, data.give);
                    data.give;
                    ();
                }
            }
        ", expect_test::expect![[r#"
            the rule "share-mutation" at (accesses.rs) failed because
              condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                &accessed_place = @ fresh(1)
                &shared_place = @ fresh(1) . a"#]])
}

/// Test where we expect data leased from self (but do nothing with it).
/// OK.
#[test]
#[allow(non_snake_case)]
fn pair_method__leased_self_ok() {
    crate::assert_ok!("
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, data: mut[self] Data) {
                  ();
                }
            }

            class Main {
                fn main(given self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.mut;
                    pair.give.method(data.give);
                    ();
                }
            }
        ")
}

/// Test where we expect data ref'd from self (but do nothing with it).
/// OK.
#[test]
#[allow(non_snake_case)]
fn pair_method__ref_self_ok() {
    crate::assert_ok!("
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, data: ref[self] Data) {
                  ();
                }
            }

            class Main {
                fn main(given self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.ref;
                    pair.give.method(data.give);
                    ();
                }
            }
        ")
}

/// Test where we expect data leased from self.a but get data from self.b.
/// Error.
#[test]
#[allow(non_snake_case)]
fn pair_method__expect_leased_self_a__got_leased_self_b() {
    crate::assert_err!("
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, data: mut[self.a] Data) {
                  ();
                }
            }

            class Main {
                fn main(given self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.b.mut;
                    pair.give.method(data.give);
                    ();
                }
            }
        ", expect_test::expect![[r#"
            the rule "(mut::P) vs (mut::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                place_b = @ fresh(0) . a
                &place_a = @ fresh(0) . b

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]])
}

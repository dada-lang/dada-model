use formality_core::test;

/// Check giving different messages in two fn calls works.
#[test]
#[allow(non_snake_case)]
fn send_two_different_messages() {
    crate::assert_ok!({
        struct Bar {}

        struct Channel[ty M] {
            fn send[perm P](P self, msg: M)
            where
              P is mut,
            {
            }
        }

        struct TheClass {
            fn empty_method(^ self) {
                let channel = new Channel[Bar]();

                let bar1 = new Bar();
                channel!.send[![channel]](bar1^);

                let bar2 = new Bar();
                channel!.send[![channel]](bar2^);

                ();
            }
        }
    })
}

/// Check that giving same message twice in fn calls errors.
#[test]
#[allow(non_snake_case)]
fn send_same_message_twice() {
    crate::assert_err!({
            struct Bar {}

            struct Channel[ty M] {
                fn send[perm P](P self, msg: M)
                where
                    P is mut,
                {
                }
            }

            struct TheClass {
                fn empty_method(^ self) {
                    let channel = new Channel[Bar]();
                    let bar = new Bar();
                    channel!.send[![channel]](bar^);
                    channel!.send[![channel]](bar^);
                    ();
                }
            }
        }, expect_test::expect![[r#"
            the rule "give" at (expressions.rs) failed because
              condition evaluted to false: `!live_after.is_live(place)`
                live_after = LivePlaces { accessed: {@ fresh(0), bar, channel}, traversed: {} }
                place = bar"#]])
}

/// Check that calling channel with a copy(self) when mut(self) is declared errors.
#[test]
#[allow(non_snake_case)]
fn needs_leased_got_shared_self() {
    crate::assert_err!({
            struct Bar {}

            struct Channel[ty M] {
                fn send[perm P](P self, msg: M)
                where
                    P is mut,
                {
                }
            }

            struct TheClass {
                fn empty_method(^ self) {
                    let channel = new Channel[Bar]();
                    let bar = new Bar();
                    channel.share.send[shared[channel]](bar^);
                    ();
                }
            }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Bar { } struct Channel [ty] { fn send [perm] (^perm0_0 self msg : ^ty1_0) -> () where ^perm0_0 is mut { } } struct TheClass { fn empty_method (^ self) -> () { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . share . send [shared [channel]] (bar ^) ; () ; } } }`"])
}

/// Test where function expects a `Pair` and data borrowed from `pair`.
/// We `give` data shared from `pair.a`.
/// OK.
#[test]
#[allow(non_snake_case)]
fn take_pair_and_data__give_pair_give_data_ok() {
    crate::assert_ok!({
        struct Data {}

        struct Pair {
            a: Data;
            b: Data;
        }

        struct TheClass {
            fn take_pair_and_data[perm P](P self, pair: ^ Pair, data: shared[pair] Data) {

            }

            fn empty_method(^ self) {
                let pair = new Pair(new Data(), new Data());
                let data = pair.a.share;
                self^.take_pair_and_data[^](pair^, data^);
                ();
            }
        }
    })
}

/// Test where function expects a `Pair` and data borrowed from `pair`.
/// We `share` data shared from `pair.a`.
/// OK.
#[test]
#[allow(non_snake_case)]
fn take_pair_and_data__give_pair_share_data_ok() {
    crate::assert_ok!({
        struct Data {}

        struct Pair {
            a: Data;
            b: Data;
        }

        struct TheClass {
            fn take_pair_and_data[perm P](P self, pair: ^ Pair, data: shared[pair] Data) {

            }

            fn empty_method(^ self) {
                let pair = new Pair(new Data(), new Data());
                let data = pair.a.share;
                self^.take_pair_and_data[^](pair^, data.share);
                ();
            }
        }
    })
}

/// Test where function expects a `Pair` and data borrowed from `pair`.
/// We `share` data shared from `pair.a` but use it later.
/// Should error because `pair` has been moved.
#[test]
#[allow(non_snake_case)]
fn take_pair_and_data__give_pair_share_data_share_later() {
    crate::assert_err!({
            struct Data {}

            struct Pair {
                a: Data;
                b: Data;
            }

            struct TheClass {
                fn take_pair_and_data[perm P](P self, pair: ^ Pair, data: shared[pair] Data) {

                }

                fn empty_method(^ self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.share;
                    self^.take_pair_and_data[^](pair^, data.share);
                    data.share;
                    ();
                }
            }
        }, expect_test::expect![[r#"
            the rule "share-mutation" at (accesses.rs) failed because
              condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
                accessed_place = @ fresh(1)
                shared_place = @ fresh(1) . a"#]])
}

/// Test where function expects a `Pair` and data borrowed from `pair`.
/// We `give` data shared from `pair.a` but use it later.
/// Should error because `pair` has been moved.
#[test]
#[allow(non_snake_case)]
fn take_pair_and_data__give_pair_give_data_give_later() {
    crate::assert_err!({
            struct Data {}

            struct Pair {
                a: Data;
                b: Data;
            }

            struct TheClass {
                fn take_pair_and_data[perm P](P self, pair: ^ Pair, data: shared[pair] Data) {

                }

                fn empty_method(^ self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.share;
                    self^.take_pair_and_data[^](pair^, data^);
                    data^;
                    ();
                }
            }
        }, expect_test::expect![[r#"
            the rule "share-mutation" at (accesses.rs) failed because
              condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
                accessed_place = @ fresh(1)
                shared_place = @ fresh(1) . a"#]])
}

/// Test where we expect data leased from self (but do nothing with it).
/// OK.
#[test]
#[allow(non_snake_case)]
fn pair_method__leased_self_ok() {
    crate::assert_ok!({
        struct Data {}

        struct Pair {
            a: Data;
            b: Data;

            fn method(^ self, data: ![self] Data) {
              ();
            }
        }

        struct Main {
            fn main(^ self) {
                let pair = new Pair(new Data(), new Data());
                let data = pair.a!;
                pair^.method(data^);
                ();
            }
        }
    })
}

/// Test where we expect data shared from from self (but do nothing with it).
/// OK.
#[test]
#[allow(non_snake_case)]
fn pair_method__ref_self_ok() {
    crate::assert_ok!({
        struct Data {}

        struct Pair {
            a: Data;
            b: Data;

            fn method(^ self, data: shared[self] Data) {
              ();
            }
        }

        struct Main {
            fn main(^ self) {
                let pair = new Pair(new Data(), new Data());
                let data = pair.a.share;
                pair^.method(data^);
                ();
            }
        }
    })
}

/// Test where we expect data leased from self.a but get data from self.b.
/// Error.
#[test]
#[allow(non_snake_case)]
fn pair_method__expect_leased_self_a__got_leased_self_b() {
    crate::assert_err!({
            struct Data {}

            struct Pair {
                a: Data;
                b: Data;

                fn method(^ self, data: ![self.a] Data) {
                  ();
                }
            }

            struct Main {
                fn main(^ self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.b!;
                    pair^.method(data^);
                    ();
                }
            }
        }, expect_test::expect![[r#"
            the rule "(mut::P) vs (mut::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(place_a)`
                place_b = @ fresh(0) . a
                place_a = @ fresh(0) . b"#]])
}

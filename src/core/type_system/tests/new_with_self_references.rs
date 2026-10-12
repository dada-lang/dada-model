use formality_core::test;

#[test]
fn choice_with_self_ref_a() {
    crate::assert_ok!({
        struct Data {
        }

        struct Pair {
            a: Data;
            b: Data;
        }

        struct Choice {
            pair: Pair;
            data: shared[self.pair] Data;
        }

        struct TheClass {
            fn empty_method(self->) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1->, d2->);
                let r = pair.a.share;
                let choice = new Choice(pair->, r->);
                ();
            }
        }
    })
}

#[test]
fn choice_with_self_ref_b() {
    crate::assert_ok!({
        struct Data {
        }

        struct Pair {
            a: Data;
            b: Data;
        }

        struct Choice {
            pair: Pair;
            data: shared[self.pair] Data;
        }

        struct TheClass {
            fn empty_method(self->) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1->, d2->);
                let r = pair.b.share;
                let choice = new Choice(pair->, r->);
                ();
            }
        }
    })
}

#[test]
fn choice_with_non_self_ref() {
    crate::assert_err!({
        struct Data {
        }

        struct Pair {
            a: Data;
            b: Data;
        }

        struct Choice {
            pair: Pair;
            data: shared[self.pair] Data;
        }

        struct TheClass {
            fn empty_method(self->) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let d3 = new Data();
                let pair = new Pair(d1->, d2->);
                let r = d3.share;
                let choice = new Choice(pair->, r->);
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "(shared[place]::P) vs (shared[place]::P)" at (redperms.rs) failed because
          condition evaluted to false: `place_b.is_prefix_of(place_a)`
            place_b = @ fresh(0) . pair
            place_a = d3"#]])
}

/// Test that we can create a `Choice`,
/// pull out its individual fields (in the correct order, mind)
/// and then reconstruct it.
///
/// In other words, when we move from `choice1.data->`
/// to `choice1_data`, we correctly track that it has type
/// `copy(choice1.pair) Data`, and then when we
/// move from `choice1.pair` to `choice1_pair`, we can adjust
/// type of `choice1_data` to be `copy(choice1_pair) Data`.
#[test]
fn unpack_and_reconstruct_correct_order() {
    crate::assert_ok!({
        struct Data {
        }

        struct Pair {
            a: Data;
            b: Data;
        }

        struct Choice {
            pair: Pair;
            data: shared[self.pair] Data;
        }

        struct TheClass {
            fn empty_method(self->) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1->, d2->);
                let r = pair.a.share;
                let choice1 = new Choice(pair->, r->);
                let choice1_data = choice1.data->;
                let choice1_pair = choice1.pair->;
                let choice2 = new Choice(choice1_pair->, choice1_data->);
                ();
            }
        }
    })
}

/// Version of `unpack_and_reconstruct_correct_order` where we pull out the
/// fields in the other order. While in principle this should work,
/// we can't handle it in our type system and we should error. Why?
/// When we move `choice1.pair` first, the type declared for `Choice::data`
/// would have to be adjusteed to reference a local variable, and that
/// doesn't work.
///
/// FIXME: We do currently get an error, but not the one I really expect us to get.
/// I think the ideal is that moving `choice1.pair` should making all of `choice1`
/// be considered moved.
#[test]
fn unpack_and_reconstruct_wrong_order() {
    crate::assert_err!({
        struct Data {
        }

        struct Pair {
            a: Data;
            b: Data;
        }

        struct Choice {
            pair: Pair;
            data: shared[self.pair] Data;
        }

        struct TheClass {
            fn empty_method(self->) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1->, d2->);
                let r = pair.a.share;
                let choice1 = new Choice(pair->, r->);
                let choice1_pair = choice1.pair->;
                let choice1_data = choice1.data->;
                let choice2 = new Choice(choice1_pair->, choice1_data->);
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = choice1 . pair
            shared_place = choice1 . pair"#]])
}

/// Access to the field `choice.pair` but the other field
/// `choice.data` has a lease on `choice.pair`.
#[test]
fn lease_when_internally_leased() {
    crate::assert_err!({
        struct Data {
        }

        struct Pair {
            a: Data;
            b: Data;
        }

        struct Choice {
            pair: Pair;
            data: ![self.pair] Data;
        }

        struct TheClass {
            fn empty_method(self->, choice: given Choice) -> () {
                let pair = choice.pair!;
                let data = choice.data!;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
            accessed_place = choice . pair
            leased_place = choice . pair"#]])
}

/// Extract the `pair` from choice and then drop it.
/// Then access data supposedly leased from that pair.
/// This should fail.
#[test]
fn unpack_and_reconstruct_drop_then_access() {
    crate::assert_err!({
        struct Data {
        }

        struct Pair {
            a: Data;
            b: Data;
        }

        struct Choice {
            pair: Pair;
            data: shared[self.pair] Data;
        }

        struct TheClass {
            fn empty_method(self->, choice: given Choice) -> () {
                let choice_pair = choice.pair->;
                choice_pair->;
                let choice_data = choice.data->;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = choice . pair
            shared_place = choice . pair"#]])
}

/// This should fail because `r` is actually a pointer to `pair`
/// so when `pair` is moved it should be invalidated. Currently it passes (FIXME#12).
#[test]
fn choice_with_leased_self_ref_a() {
    crate::assert_ok!({
        struct Data {
        }

        struct Pair {
            a: Data;
            b: Data;
        }

        struct Choice {
            pair: Pair;
            data: ![self.pair] Data;
        }

        struct TheClass {
            fn empty_method(self->) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1->, d2->);
                let r = pair.a!;
                let choice = new Choice(pair->, r->);
                ();
            }
        }
    })
}

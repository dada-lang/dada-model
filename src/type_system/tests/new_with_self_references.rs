use formality_core::test;

#[test]
fn choice_with_self_ref_a() {
    crate::assert_ok!({
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: ref[self.pair] Data;
        }

        class TheClass {
            fn empty_method(given self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.give, d2.give);
                let r = pair.a.ref;
                let choice = new Choice(pair.give, r.give);
                ();
            }
        }
    })
}

#[test]
fn choice_with_self_ref_b() {
    crate::assert_ok!({
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: ref[self.pair] Data;
        }

        class TheClass {
            fn empty_method(given self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.give, d2.give);
                let r = pair.b.ref;
                let choice = new Choice(pair.give, r.give);
                ();
            }
        }
    })
}

#[test]
fn choice_with_non_self_ref() {
    crate::assert_err!({
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: ref[self.pair] Data;
        }

        class TheClass {
            fn empty_method(given self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let d3 = new Data();
                let pair = new Pair(d1.give, d2.give);
                let r = d3.ref;
                let choice = new Choice(pair.give, r.give);
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "parameter" at (predicates.rs) failed because
          pattern `true` did not match value `false`

        the rule "(ref::P) vs (ref::P)" at (redperms.rs) failed because
          condition evaluted to false: `place_b.is_prefix_of(&place_a)`
            place_b = @ fresh(0) . pair
            &place_a = d3

        the rule "parameter" at (predicates.rs) failed because
          pattern `true` did not match value `false`"#]])
}

/// Test that we can create a `Choice`,
/// pull out its individual fields (in the correct order, mind)
/// and then reconstruct it.
///
/// In other words, when we move from `choice1.data.give`
/// to `choice1_data`, we correctly track that it has type
/// `copy(choice1.pair) Data`, and then when we
/// move from `choice1.pair` to `choice1_pair`, we can adjust
/// type of `choice1_data` to be `copy(choice1_pair) Data`.
#[test]
fn unpack_and_reconstruct_correct_order() {
    crate::assert_ok!({
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: ref[self.pair] Data;
        }

        class TheClass {
            fn empty_method(given self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.give, d2.give);
                let r = pair.a.ref;
                let choice1 = new Choice(pair.give, r.give);
                let choice1_data = choice1.data.give;
                let choice1_pair = choice1.pair.give;
                let choice2 = new Choice(choice1_pair.give, choice1_data.give);
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
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: ref[self.pair] Data;
        }

        class TheClass {
            fn empty_method(given self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.give, d2.give);
                let r = pair.a.ref;
                let choice1 = new Choice(pair.give, r.give);
                let choice1_pair = choice1.pair.give; 
                let choice1_data = choice1.data.give;
                let choice2 = new Choice(choice1_pair.give, choice1_data.give);
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
            &accessed_place = choice1 . pair
            &shared_place = choice1 . pair"#]])
}

/// Access to the field `choice.pair` but the other field
/// `choice.data` has a lease on `choice.pair`.
#[test]
fn lease_when_internally_leased() {
    crate::assert_err!({
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: mut[self.pair] Data;
        }

        class TheClass {
            fn empty_method(given self, choice: Choice) -> () {
                let pair = choice.pair.mut;
                let data = choice.data.mut;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
            &accessed_place = choice . pair
            &leased_place = choice . pair"#]])
}

/// Extract the `pair` from choice and then drop it.
/// Then access data supposedly leased from that pair.
/// This should fail.
#[test]
fn unpack_and_reconstruct_drop_then_access() {
    crate::assert_err!({
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: ref[self.pair] Data;
        }

        class TheClass {
            fn empty_method(given self, choice: Choice) -> () {
                let choice_pair = choice.pair.give; 
                choice_pair.give;
                let choice_data = choice.data.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
            &accessed_place = choice . pair
            &shared_place = choice . pair"#]])
}

/// This should fail because `r` is actually a pointer to `pair`
/// so when `pair` is moved it should be invalidated. Currently it passes (FIXME#12).
#[test]
fn choice_with_leased_self_ref_a() {
    crate::assert_ok!({
        class Data {
        }

        class Pair {
            a: Data;
            b: Data;
        }

        class Choice {
            pair: Pair;
            data: mut[self.pair] Data;
        }

        class TheClass {
            fn empty_method(given self) -> () {
                let d1 = new Data();
                let d2 = new Data();
                let pair = new Pair(d1.give, d2.give);
                let r = pair.a.mut;
                let choice = new Choice(pair.give, r.give);
                ();
            }
        }
    })
}

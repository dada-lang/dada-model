//! ## All possible return referents remain borrowed
//!
//! When a method's return signature names several possible borrowed origins,
//! each corresponding caller referent remains borrowed while the returned value
//! is live. This restriction follows the signature even when the method body
//! always returns a borrow of its first argument.
//!
//! Here `x` and `y` are the callee's parameter bindings; `d1` and `d2` are the
//! caller's referents. Returning `ref[x, y]` or `![x, y]` through borrowed
//! arguments must retain the dependencies on both `d1` and `d2` after the call's
//! temporary bindings disappear. The callee's use of `x` alone does not let the
//! caller disregard `y`'s declared contribution to the result.
//!
//! ### Evidence and scope
//!
//! Complete Dada programs check each referent independently for shared returns,
//! mutable returns, and shared returns through mutable arguments. A live shared
//! result prevents discarding either referent; a live result returned through
//! mutable arguments prevents mutably reborrowing either referent. Each rejection
//! has a control performing the same access after the result's last use.
//! Another control consumes both referents after the result's last use.
//!
//! The standalone `d1.give;` and `d2.give;` statements discard their values.
//! Their rejection does not say that every move is forbidden: a move into a new
//! binding can relocate a referent and its borrowing dependencies, as described
//! by `moves_preserve_dependencies`.
//!
//! All accepting programs type-check and execute. Shared field reads print `42`
//! from the first argument, and the mutable result prints `43` after assignment.
//! Every accepting program returns unit and leaves no live allocations.
//! These snapshots observe the referent actually returned; the rejection tests
//! separately establish static borrowing restrictions on both possible referents.
//!
//! These examples use ordinary non-shared classes and two direct borrowed
//! arguments. They provide static and runtime evidence for these programs,
//! not a proof for arbitrary signatures, all runtime choices, or pointer relocation.

use formality_core::test;

/// A shared return naming both shared-borrowed arguments permits reading a field.
#[test]
fn shared_return_accepts_two_borrowed_arguments() {
    crate::assert_interpret!({
        class Data { n: Int; }
        class Funcs {
            fn either[perm P, perm Q](^ self, x: P Data, y: Q Data) -> ref[x, y] Data
            where P is shared, Q is shared
            {
                x.ref;
            }
        }
        class Main {
            fn main(^ self) {
                let d1 = new Data(42);
                let d2 = new Data(99);
                let f = new Funcs();
                let result = f.give.either[ref[d1], ref[d2]](d1.ref, d2.ref);
                print(result.n.give);
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d1 = new Data (42) ;
        Output: Trace:   _1_d1 = Data { n: 42 }
        Output: Trace:   let _1_d2 = new Data (99) ;
        Output: Trace:   _1_d2 = Data { n: 99 }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_result = _1_f . give . either [ref [_1_d1], ref [_1_d2]] (_1_d1 . ref, _1_d2 . ref) ;
        Output: Trace:   enter Funcs.either
        Output: Trace:     _2_x . ref ;
        Output: Trace:   exit Funcs.either => ref [_1_d1] Data { n: 42 }
        Output: Trace:   _1_result = ref [_1_d1] Data { n: 42 }
        Output: Trace:   print(_1_result . n . give) ;
        Output: ----->   42
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

/// Discarding the first referent conflicts with the live shared result.
#[test]
fn shared_return_blocks_discarding_first_referent() {
    crate::assert_err!({
        class Data {}
        class Funcs {
            fn either[perm P, perm Q](^ self, x: P Data, y: Q Data) -> ref[x, y] Data
            where P is shared, Q is shared
            {
                x.ref;
            }
        }
        class Main {
            fn go(^ self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.either[ref[d1], ref[d2]](d1.ref, d2.ref);
                d1.give;
                result.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = @ fresh(0)
            shared_place = @ fresh(0)"#]]);
}

/// After the result's last use, the same access to the first referent succeeds.
#[test]
fn shared_return_allows_discarding_first_referent_after_last_use() {
    crate::assert_interpret!({
        class Data {}
        class Funcs {
            fn either[perm P, perm Q](^ self, x: P Data, y: Q Data) -> ref[x, y] Data
            where P is shared, Q is shared
            {
                x.ref;
            }
        }
        class Main {
            fn main(^ self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.either[ref[d1], ref[d2]](d1.ref, d2.ref);
                result.give;
                d1.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d1 = new Data () ;
        Output: Trace:   _1_d1 = Data {  }
        Output: Trace:   let _1_d2 = new Data () ;
        Output: Trace:   _1_d2 = Data {  }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_result = _1_f . give . either [ref [_1_d1], ref [_1_d2]] (_1_d1 . ref, _1_d2 . ref) ;
        Output: Trace:   enter Funcs.either
        Output: Trace:     _2_x . ref ;
        Output: Trace:   exit Funcs.either => ref [_1_d1] Data {  }
        Output: Trace:   _1_result = ref [_1_d1] Data {  }
        Output: Trace:   _1_result . give ;
        Output: Trace:   _1_d1 . give ;
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

/// Discarding the second referent conflicts with the live shared result.
#[test]
fn shared_return_blocks_discarding_second_referent() {
    crate::assert_err!({
        class Data {}
        class Funcs {
            fn either[perm P, perm Q](^ self, x: P Data, y: Q Data) -> ref[x, y] Data
            where P is shared, Q is shared
            {
                x.ref;
            }
        }
        class Main {
            fn go(^ self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.either[ref[d1], ref[d2]](d1.ref, d2.ref);
                d2.give;
                result.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = @ fresh(0)
            shared_place = @ fresh(0)"#]]);
}

/// After the result's last use, the same access to the second referent succeeds.
#[test]
fn shared_return_allows_discarding_second_referent_after_last_use() {
    crate::assert_interpret!({
        class Data {}
        class Funcs {
            fn either[perm P, perm Q](^ self, x: P Data, y: Q Data) -> ref[x, y] Data
            where P is shared, Q is shared
            {
                x.ref;
            }
        }
        class Main {
            fn main(^ self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.either[ref[d1], ref[d2]](d1.ref, d2.ref);
                result.give;
                d2.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d1 = new Data () ;
        Output: Trace:   _1_d1 = Data {  }
        Output: Trace:   let _1_d2 = new Data () ;
        Output: Trace:   _1_d2 = Data {  }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_result = _1_f . give . either [ref [_1_d1], ref [_1_d2]] (_1_d1 . ref, _1_d2 . ref) ;
        Output: Trace:   enter Funcs.either
        Output: Trace:     _2_x . ref ;
        Output: Trace:   exit Funcs.either => ref [_1_d1] Data {  }
        Output: Trace:   _1_result = ref [_1_d1] Data {  }
        Output: Trace:   _1_result . give ;
        Output: Trace:   _1_d2 . give ;
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

/// Both referents can be consumed after the returned borrow has its last use.
#[test]
fn shared_return_releases_both_referents_after_last_use() {
    crate::assert_interpret!({
        class Data {}
        class Funcs {
            fn either[perm P, perm Q](^ self, x: P Data, y: Q Data) -> ref[x, y] Data
            where P is shared, Q is shared
            {
                x.ref;
            }
        }
        class Sink {
            fn consume(^ self, d: ^ Data) { (); }
        }
        class Main {
            fn main(^ self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.either[ref[d1], ref[d2]](d1.ref, d2.ref);
                result.give;
                let sink1 = new Sink();
                sink1.give.consume(d1.give);
                let sink2 = new Sink();
                sink2.give.consume(d2.give);
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d1 = new Data () ;
        Output: Trace:   _1_d1 = Data {  }
        Output: Trace:   let _1_d2 = new Data () ;
        Output: Trace:   _1_d2 = Data {  }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_result = _1_f . give . either [ref [_1_d1], ref [_1_d2]] (_1_d1 . ref, _1_d2 . ref) ;
        Output: Trace:   enter Funcs.either
        Output: Trace:     _2_x . ref ;
        Output: Trace:   exit Funcs.either => ref [_1_d1] Data {  }
        Output: Trace:   _1_result = ref [_1_d1] Data {  }
        Output: Trace:   _1_result . give ;
        Output: Trace:   let _1_sink1 = new Sink () ;
        Output: Trace:   _1_sink1 = Sink {  }
        Output: Trace:   _1_sink1 . give . consume (_1_d1 . give) ;
        Output: Trace:   enter Sink.consume
        Output: Trace:     () ;
        Output: Trace:   exit Sink.consume => ()
        Output: Trace:   let _1_sink2 = new Sink () ;
        Output: Trace:   _1_sink2 = Sink {  }
        Output: Trace:   _1_sink2 . give . consume (_1_d2 . give) ;
        Output: Trace:   enter Sink.consume
        Output: Trace:     () ;
        Output: Trace:   exit Sink.consume => ()
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

/// A mutable return naming both borrowed arguments permits writing and reading a field.
#[test]
fn mutable_return_accepts_two_mutably_borrowed_arguments() {
    crate::assert_interpret!({
        class Data { n: Int; }
        class Funcs {
            fn either[perm P, perm Q](^ self, x: P Data, y: Q Data) -> ![x, y] Data
            where P is mut, Q is mut
            {
                x.mut;
            }
        }
        class Main {
            fn main(^ self) {
                let d1 = new Data(42);
                let d2 = new Data(99);
                let f = new Funcs();
                let result = f.give.either[![d1], ![d2]](d1.mut, d2.mut);
                result.n = 43;
                print(result.n.give);
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d1 = new Data (42) ;
        Output: Trace:   _1_d1 = Data { n: 42 }
        Output: Trace:   let _1_d2 = new Data (99) ;
        Output: Trace:   _1_d2 = Data { n: 99 }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_result = _1_f . give . either [! [_1_d1], ! [_1_d2]] (_1_d1 . mut, _1_d2 . mut) ;
        Output: Trace:   enter Funcs.either
        Output: Trace:     _2_x . mut ;
        Output: Trace:   exit Funcs.either => ! [_1_d1] Data { n: 42 }
        Output: Trace:   _1_result = ! [_1_d1] Data { n: 42 }
        Output: Trace:   _1_result . n = 43 ;
        Output: Trace:   _1_result . n = 43
        Output: Trace:   print(_1_result . n . give) ;
        Output: ----->   43
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

/// Mutably reborrowing the first referent conflicts with the live mutable result.
#[test]
fn mutable_return_blocks_mutably_reborrowing_first_referent() {
    crate::assert_err!({
        class Data {}
        class Funcs {
            fn either[perm P, perm Q](^ self, x: P Data, y: Q Data) -> ![x, y] Data
            where P is mut, Q is mut
            {
                x.mut;
            }
        }
        class Main {
            fn go(^ self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.either[![d1], ![d2]](d1.mut, d2.mut);
                d1.mut;
                result.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
            accessed_place = d1
            leased_place = d1"#]]);
}

/// After the result's last use, the same access to the first referent succeeds.
#[test]
fn mutable_return_allows_mutably_reborrowing_first_referent_after_last_use() {
    crate::assert_interpret!({
        class Data {}
        class Funcs {
            fn either[perm P, perm Q](^ self, x: P Data, y: Q Data) -> ![x, y] Data
            where P is mut, Q is mut
            {
                x.mut;
            }
        }
        class Main {
            fn main(^ self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.either[![d1], ![d2]](d1.mut, d2.mut);
                result.give;
                d1.mut;
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d1 = new Data () ;
        Output: Trace:   _1_d1 = Data {  }
        Output: Trace:   let _1_d2 = new Data () ;
        Output: Trace:   _1_d2 = Data {  }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_result = _1_f . give . either [! [_1_d1], ! [_1_d2]] (_1_d1 . mut, _1_d2 . mut) ;
        Output: Trace:   enter Funcs.either
        Output: Trace:     _2_x . mut ;
        Output: Trace:   exit Funcs.either => ! [_1_d1] Data {  }
        Output: Trace:   _1_result = ! [_1_d1] Data {  }
        Output: Trace:   _1_result . give ;
        Output: Trace:   _1_d1 . mut ;
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

/// Mutably reborrowing the second referent conflicts with the live mutable result.
#[test]
fn mutable_return_blocks_mutably_reborrowing_second_referent() {
    crate::assert_err!({
        class Data {}
        class Funcs {
            fn either[perm P, perm Q](^ self, x: P Data, y: Q Data) -> ![x, y] Data
            where P is mut, Q is mut
            {
                x.mut;
            }
        }
        class Main {
            fn go(^ self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.either[![d1], ![d2]](d1.mut, d2.mut);
                d2.mut;
                result.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
            accessed_place = d2
            leased_place = d2"#]]);
}

/// After the result's last use, the same access to the second referent succeeds.
#[test]
fn mutable_return_allows_mutably_reborrowing_second_referent_after_last_use() {
    crate::assert_interpret!({
        class Data {}
        class Funcs {
            fn either[perm P, perm Q](^ self, x: P Data, y: Q Data) -> ![x, y] Data
            where P is mut, Q is mut
            {
                x.mut;
            }
        }
        class Main {
            fn main(^ self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.either[![d1], ![d2]](d1.mut, d2.mut);
                result.give;
                d2.mut;
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d1 = new Data () ;
        Output: Trace:   _1_d1 = Data {  }
        Output: Trace:   let _1_d2 = new Data () ;
        Output: Trace:   _1_d2 = Data {  }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_result = _1_f . give . either [! [_1_d1], ! [_1_d2]] (_1_d1 . mut, _1_d2 . mut) ;
        Output: Trace:   enter Funcs.either
        Output: Trace:     _2_x . mut ;
        Output: Trace:   exit Funcs.either => ! [_1_d1] Data {  }
        Output: Trace:   _1_result = ! [_1_d1] Data {  }
        Output: Trace:   _1_result . give ;
        Output: Trace:   _1_d2 . mut ;
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

/// A shared return naming both mutably borrowed arguments permits reading a field.
#[test]
fn shared_return_accepts_two_mutably_borrowed_arguments() {
    crate::assert_interpret!({
        class Data { n: Int; }
        class Funcs {
            fn either[perm P, perm Q](^ self, x: P Data, y: Q Data) -> ref[x, y] Data
            where P is mut, Q is mut
            {
                x.ref;
            }
        }
        class Main {
            fn main(^ self) {
                let d1 = new Data(42);
                let d2 = new Data(99);
                let f = new Funcs();
                let result = f.give.either[![d1], ![d2]](d1.mut, d2.mut);
                print(result.n.give);
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d1 = new Data (42) ;
        Output: Trace:   _1_d1 = Data { n: 42 }
        Output: Trace:   let _1_d2 = new Data (99) ;
        Output: Trace:   _1_d2 = Data { n: 99 }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_result = _1_f . give . either [! [_1_d1], ! [_1_d2]] (_1_d1 . mut, _1_d2 . mut) ;
        Output: Trace:   enter Funcs.either
        Output: Trace:     _2_x . ref ;
        Output: Trace:   exit Funcs.either => shared ! [_1_d1] Data { n: 42 }
        Output: Trace:   _1_result = shared ! [_1_d1] Data { n: 42 }
        Output: Trace:   print(_1_result . n . give) ;
        Output: ----->   42
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

/// A shared return through mutable arguments keeps the first referent borrowed.
#[test]
fn shared_return_through_mut_blocks_mutably_reborrowing_first_referent() {
    crate::assert_err!({
        class Data {}
        class Funcs {
            fn either[perm P, perm Q](^ self, x: P Data, y: Q Data) -> ref[x, y] Data
            where P is mut, Q is mut
            {
                x.ref;
            }
        }
        class Main {
            fn go(^ self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.either[![d1], ![d2]](d1.mut, d2.mut);
                d1.mut;
                result.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
            accessed_place = d1
            leased_place = d1"#]]);
}

/// After the result's last use, the same access to the first referent succeeds.
#[test]
fn shared_return_through_mut_allows_mutably_reborrowing_first_referent_after_last_use() {
    crate::assert_interpret!({
        class Data {}
        class Funcs {
            fn either[perm P, perm Q](^ self, x: P Data, y: Q Data) -> ref[x, y] Data
            where P is mut, Q is mut
            {
                x.ref;
            }
        }
        class Main {
            fn main(^ self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.either[![d1], ![d2]](d1.mut, d2.mut);
                result.give;
                d1.mut;
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d1 = new Data () ;
        Output: Trace:   _1_d1 = Data {  }
        Output: Trace:   let _1_d2 = new Data () ;
        Output: Trace:   _1_d2 = Data {  }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_result = _1_f . give . either [! [_1_d1], ! [_1_d2]] (_1_d1 . mut, _1_d2 . mut) ;
        Output: Trace:   enter Funcs.either
        Output: Trace:     _2_x . ref ;
        Output: Trace:   exit Funcs.either => shared ! [_1_d1] Data {  }
        Output: Trace:   _1_result = shared ! [_1_d1] Data {  }
        Output: Trace:   _1_result . give ;
        Output: Trace:   _1_d1 . mut ;
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

/// A shared return through mutable arguments keeps the second referent borrowed.
#[test]
fn shared_return_through_mut_blocks_mutably_reborrowing_second_referent() {
    crate::assert_err!({
        class Data {}
        class Funcs {
            fn either[perm P, perm Q](^ self, x: P Data, y: Q Data) -> ref[x, y] Data
            where P is mut, Q is mut
            {
                x.ref;
            }
        }
        class Main {
            fn go(^ self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.either[![d1], ![d2]](d1.mut, d2.mut);
                d2.mut;
                result.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
            accessed_place = d2
            leased_place = d2"#]]);
}

/// After the result's last use, the same access to the second referent succeeds.
#[test]
fn shared_return_through_mut_allows_mutably_reborrowing_second_referent_after_last_use() {
    crate::assert_interpret!({
        class Data {}
        class Funcs {
            fn either[perm P, perm Q](^ self, x: P Data, y: Q Data) -> ref[x, y] Data
            where P is mut, Q is mut
            {
                x.ref;
            }
        }
        class Main {
            fn main(^ self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.either[![d1], ![d2]](d1.mut, d2.mut);
                result.give;
                d2.mut;
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d1 = new Data () ;
        Output: Trace:   _1_d1 = Data {  }
        Output: Trace:   let _1_d2 = new Data () ;
        Output: Trace:   _1_d2 = Data {  }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_result = _1_f . give . either [! [_1_d1], ! [_1_d2]] (_1_d1 . mut, _1_d2 . mut) ;
        Output: Trace:   enter Funcs.either
        Output: Trace:     _2_x . ref ;
        Output: Trace:   exit Funcs.either => shared ! [_1_d1] Data {  }
        Output: Trace:   _1_result = shared ! [_1_d1] Data {  }
        Output: Trace:   _1_result . give ;
        Output: Trace:   _1_d2 . mut ;
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

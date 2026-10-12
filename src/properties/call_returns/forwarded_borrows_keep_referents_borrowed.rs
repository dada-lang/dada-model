//! ## Forwarded borrows keep their referents borrowed
//!
//! When a method returns a borrow through one of its borrowed parameters, the
//! caller's referent remains borrowed while the returned value is live. The
//! method parameter need not remain in scope: resolving the return permission
//! carries its borrowing dependency back to the caller's referent.
//!
//! A shared borrow returned through a shared-borrowed argument permits another
//! shared borrow of the referent but prevents mutable access. A mutable borrow
//! returned through a mutably borrowed argument prevents both shared and mutable
//! access to the referent. Disjoint fields remain accessible, and the restrictions
//! cease after the returned value's last use. Returning a shared view through a
//! mutable argument can retain the underlying mutable borrowing restrictions;
//! that composition is covered in the alternative-referent property.
//!
//! ### Evidence and scope
//!
//! Complete Dada programs forward shared borrows through a named parameter and
//! a receiver, then read an integer field through the returned value with
//! `print(result.n->)`. Both programs type-check, execute, and print `42`.
//! Paired accepting and rejecting programs check access to a single
//! caller-owned referent while the returned borrow is live and after its last
//! use. A projected mutable-borrow example checks that a disjoint sibling field
//! remains accessible. All accepting programs execute successfully, return
//! unit, and leave no live allocations; rejecting programs assert the static
//! borrowing conflict.
//!
//! These tests use ordinary non-shared structs and single-origin return
//! permissions. They demonstrate static access restrictions and successful
//! execution for these examples, not a proved preservation theorem or all
//! runtime pointer behavior. Alternative return origins are covered by
//! `all_possible_return_referents_remain_borrowed`.

use formality_core::test;

/// Method returns shared[x] where x is passed as place sharing → borrow chains through.
/// Result should be shared[d] in the caller's scope.
#[test]
fn borrow_chain_ref_through_ref() {
    crate::assert_interpret!({
        struct Data { n: Int; }
        struct Funcs {
            fn borrow[perm P](given self, x: P Data) -> shared[x] Data
            where P is shared
            {
                x.share;
            }
        }
        struct Main {
            fn main(given self) {
                let d = new Data(42);
                let f = new Funcs();
                let result = f->.borrow[shared[d]](d.share);
                print(result.n->);
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d = new Data (42) ;
        Output: Trace:   _1_d = Data { n: 42 }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_result = _1_f -> . borrow [shared [_1_d]] (_1_d . share) ;
        Output: Trace:   enter Funcs.borrow
        Output: Trace:     _2_x . share ;
        Output: Trace:   exit Funcs.borrow => shared [_1_d] Data { n: 42 }
        Output: Trace:   _1_result = shared [_1_d] Data { n: 42 }
        Output: Trace:   print(_1_result . n ->) ;
        Output: ----->   42
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

/// Method returns shared[self] where self is passed as place sharing → borrow chains.
#[test]
fn borrow_chain_ref_through_ref_self() {
    crate::assert_interpret!({
        struct Data { n: Int; }
        struct Container {
            d: given Data;
            fn get[perm P](P self) -> shared[self] Data
            where P is shared
            {
                self.d.share;
            }
        }
        struct Main {
            fn main(given self) {
                let c = new Container(new Data(42));
                let result = c.share.get[shared[c]]();
                print(result.n->);
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_c = new Container (new Data (42)) ;
        Output: Trace:   _1_c = Container { d: Data { n: 42 } }
        Output: Trace:   let _1_result = _1_c . share . get [shared [_1_c]] () ;
        Output: Trace:   enter Container.get
        Output: Trace:     _2_self . d . share ;
        Output: Trace:   exit Container.get => shared [_1_c] Data { n: 42 }
        Output: Trace:   _1_result = shared [_1_c] Data { n: 42 }
        Output: Trace:   print(_1_result . n ->) ;
        Output: ----->   42
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

#[test]
fn returned_ref_blocks_mutable_access() {
    crate::assert_err!({
        struct Data {}
        struct Funcs {
            fn borrow[perm P](given self, x: P Data) -> shared[x] Data
            where P is shared
            {
                x.share;
            }
        }
        struct Main {
            fn go(given self) {
                let d = new Data();
                let f = new Funcs();
                let result = f->.borrow[shared[d]](d.share);
                d!;
                result->;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = d
            shared_place = d"#]]);
}

#[test]
fn returned_ref_allows_shared_access() {
    crate::assert_interpret!({
        struct Data {}
        struct Funcs {
            fn borrow[perm P](given self, x: P Data) -> shared[x] Data
            where P is shared
            {
                x.share;
            }
        }
        struct Main {
            fn main(given self) {
                let d = new Data();
                let f = new Funcs();
                let result = f->.borrow[shared[d]](d.share);
                d.share;
                result->;
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d = new Data () ;
        Output: Trace:   _1_d = Data {  }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_result = _1_f -> . borrow [shared [_1_d]] (_1_d . share) ;
        Output: Trace:   enter Funcs.borrow
        Output: Trace:     _2_x . share ;
        Output: Trace:   exit Funcs.borrow => shared [_1_d] Data {  }
        Output: Trace:   _1_result = shared [_1_d] Data {  }
        Output: Trace:   _1_d . share ;
        Output: Trace:   _1_result -> ;
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

#[test]
fn returned_ref_releases_referent_after_last_use() {
    crate::assert_interpret!({
        struct Data {}
        struct Funcs {
            fn borrow[perm P](given self, x: P Data) -> shared[x] Data
            where P is shared
            {
                x.share;
            }
        }
        struct Main {
            fn main(given self) {
                let d = new Data();
                let f = new Funcs();
                let result = f->.borrow[shared[d]](d.share);
                result->;
                d!;
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d = new Data () ;
        Output: Trace:   _1_d = Data {  }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_result = _1_f -> . borrow [shared [_1_d]] (_1_d . share) ;
        Output: Trace:   enter Funcs.borrow
        Output: Trace:     _2_x . share ;
        Output: Trace:   exit Funcs.borrow => shared [_1_d] Data {  }
        Output: Trace:   _1_result = shared [_1_d] Data {  }
        Output: Trace:   _1_result -> ;
        Output: Trace:   _1_d ! ;
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

#[test]
fn returned_ref_from_receiver_keeps_receiver_borrowed() {
    crate::assert_err!({
        struct Data {}
        struct Container {
            d: given Data;
            fn get[perm P](P self) -> shared[self] Data
            where P is shared
            {
                self.d.share;
            }
        }
        struct Main {
            fn go(given self) {
                let c = new Container(new Data());
                let result = c.share.get[shared[c]]();
                c.d!;
                result->;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = c . d
            shared_place = c"#]]);
}

#[test]
fn returned_mut_blocks_shared_access() {
    crate::assert_err!({
        struct Data {}
        struct Funcs {
            fn borrow[perm P](given self, x: P Data) -> ![x] Data
            where P is mut
            {
                x!;
            }
        }
        struct Main {
            fn go(given self) {
                let d = new Data();
                let f = new Funcs();
                let result = f->.borrow[![d]](d!);
                d.share;
                result->;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
            accessed_place = d
            leased_place = d"#]]);
}

#[test]
fn returned_mut_blocks_mutable_access() {
    crate::assert_err!({
        struct Data {}
        struct Funcs {
            fn borrow[perm P](given self, x: P Data) -> ![x] Data
            where P is mut
            {
                x!;
            }
        }
        struct Main {
            fn go(given self) {
                let d = new Data();
                let f = new Funcs();
                let result = f->.borrow[![d]](d!);
                d!;
                result->;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
            accessed_place = d
            leased_place = d"#]]);
}

#[test]
fn returned_mut_releases_referent_after_last_use() {
    crate::assert_interpret!({
        struct Data {}
        struct Funcs {
            fn borrow[perm P](given self, x: P Data) -> ![x] Data
            where P is mut
            {
                x!;
            }
        }
        struct Main {
            fn main(given self) {
                let d = new Data();
                let f = new Funcs();
                let result = f->.borrow[![d]](d!);
                result->;
                d.share;
                d!;
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d = new Data () ;
        Output: Trace:   _1_d = Data {  }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_result = _1_f -> . borrow [! [_1_d]] (_1_d !) ;
        Output: Trace:   enter Funcs.borrow
        Output: Trace:     _2_x ! ;
        Output: Trace:   exit Funcs.borrow => ! [_1_d] Data {  }
        Output: Trace:   _1_result = ! [_1_d] Data {  }
        Output: Trace:   _1_result -> ;
        Output: Trace:   _1_d . share ;
        Output: Trace:   _1_d ! ;
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

#[test]
fn returned_mut_allows_disjoint_sibling_access() {
    crate::assert_interpret!({
        struct Data {}
        struct Container { field: given Data; other: given Data; }
        struct Funcs {
            fn borrow[perm P](given self, x: P Data) -> ![x] Data
            where P is mut
            {
                x!;
            }
        }
        struct Main {
            fn main(given self) {
                let c = new Container(new Data(), new Data());
                let f = new Funcs();
                let result = f->.borrow[![c.field]](c.field!);
                c.other.share;
                c.other!;
                result->;
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_c = new Container (new Data (), new Data ()) ;
        Output: Trace:   _1_c = Container { field: Data {  }, other: Data {  } }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_result = _1_f -> . borrow [! [_1_c . field]] (_1_c . field !) ;
        Output: Trace:   enter Funcs.borrow
        Output: Trace:     _2_x ! ;
        Output: Trace:   exit Funcs.borrow => ! [_1_c . field] Data {  }
        Output: Trace:   _1_result = ! [_1_c . field] Data {  }
        Output: Trace:   _1_c . other . share ;
        Output: Trace:   _1_c . other ! ;
        Output: Trace:   _1_result -> ;
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

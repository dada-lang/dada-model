//! # Explicit drops respect live dependencies
//!
//! A place with a live share cannot be explicitly dropped. Once the share's last
//! use has passed, dropping the place is permitted and runs its destructor.
//! These paired programs exercise the surface drop statement through lowering,
//! liveness, type checking, and interpretation; the accepted case also checks
//! that the destructor runs at the explicit drop rather than at scope exit.

#[test]
fn drop_after_last_shared_use_runs_destructor() {
    crate::assert_interpret!(
        {
            class Data {
                x: Int;
                drop { print(99); }
            }
            struct Main {
                fn main(^ self) -> () {
                    let d = new Data(42);
                    let s = d.share;
                    print(s.x^);
                    drop d;
                    print(7);
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (42) ;
            Output: Trace:   _1_d = Data { x: 42 }
            Output: Trace:   let _1_s = _1_d . share ;
            Output: Trace:   _1_s = shared [_1_d] Data { x: 42 }
            Output: Trace:   print(_1_s . x ^) ;
            Output: ----->   42
            Output: Trace:   drop _1_d ;
            Output: Trace:   drop Data
            Output: Trace:     print(99) ;
            Output: ----->     99
            Output: Trace:   print(7) ;
            Output: ----->   7
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn drop_before_last_shared_use_is_rejected() {
    crate::assert_err!(
        {
            class Data {
                x: Int;
                drop { print(99); }
            }
            struct Main {
                fn main(^ self) -> () {
                    let d = new Data(42);
                    let s = d.share;
                    drop d;
                    print(s.x^);
                    print(7);
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            the rule "share-mutation" at (accesses.rs) failed because
              condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
                accessed_place = d
                shared_place = d"#]]
    );
}

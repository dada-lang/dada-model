//! ## Borrows of consumed arguments cannot escape a call
//!
//! A call cannot return a borrow whose referent is a uniquely owned argument
//! destroyed when the call returns. For an ordinary non-shared `Data`, passing
//! `d→` to a parameter `x: given Data` does not permit the call to return
//! `shared[x] Data`. The caller's former ownership of `d` does not keep that consumed
//! argument alive.
//!
//! Every possible referent in the return permission must survive. A return type
//! `shared[x, y] Data` is rejected when either argument is consumed in this way,
//! even when the method body returns only a borrow of the other argument.
//!
//! The contrasting case passes `d.share` to the same generic method. The returned
//! borrow can then refer to `d`, which remains in the caller, instead of depending
//! on the temporary parameter binding. Merely naming a parameter in the return
//! permission does not make its borrow invalid.
//!
//! ### Evidence and scope
//!
//! Complete Dada programs check a consumed receiver, a named argument, two
//! consumed arguments, and one borrowed argument paired with a consumed one.
//! A positive/negative pair uses the identical generic method returning `shared[x]`
//! and changes its argument from `d.share` to `d→` (and the corresponding
//! permission argument). Both programs attempt to read the result's integer field
//! with `print(result.n→)`; the borrowed-argument program type-checks and
//! executes, printing `42`, while the given-argument program is rejected at the
//! call. The other rejected calls
//! report dangling borrows even when their results are unused.
//!
//! This property concerns static rejection of borrows of destroyed `given`
//! arguments. It does not claim that references to all owned values must be
//! rejected: shared ownership can survive independently. The evidence uses
//! ordinary non-shared structs. Execution of the valid control does not prove
//! general runtime destruction behavior or cover every permission composition.

use formality_core::test;

/// Method returns shared[self] where self is given → dangling borrow.
/// The place sharing borrows from an owned value that will be dropped when the method returns.
#[test]
fn dangling_borrow_ref_from_given_self() {
    crate::assert_err!(
        r#"
        struct Data {}
        struct Container {
            d: given Data;
            fn get(given self) → shared[self] Data {
                self.d.share;
            }
        }
        struct Main {
            fn go(given self) {
                let c = new Container(new Data());
                let result = c→.get();
                ();
            }
        }
    "#,
        expect_test::expect![[r#"
        the rule "call" at (expressions.rs) failed because
          dangling borrow: @ fresh(0) has no mut-based tail in RedChain { links: [ShareDead(@ fresh(0))] }"#]]
    );
}

/// Method returns shared[x] where x is a given parameter → dangling borrow.
#[test]
fn dangling_borrow_ref_from_given_param() {
    crate::assert_err!(
        r#"
        struct Data {}
        struct Funcs {
            fn borrow(given self, x: given Data) → shared[x] Data {
                x.share;
            }
        }
        struct Main {
            fn go(given self) {
                let d = new Data();
                let f = new Funcs();
                let result = f→.borrow(d→);
                ();
            }
        }
    "#,
        expect_test::expect![[r#"
        the rule "call" at (expressions.rs) failed because
          dangling borrow: @ fresh(1) has no mut-based tail in RedChain { links: [ShareDead(@ fresh(1))] }"#]]
    );
}

/// Multi-place shared[x, y] where both x and y are given → dangling borrow.
/// Both branches dangle — must be an error.
#[test]
fn dangling_borrow_ref_from_two_given_params() {
    crate::assert_err!(
        r#"
        struct Data {}
        struct Funcs {
            fn either(given self, x: given Data, y: given Data) → shared[x, y] Data {
                x.share;
            }
        }
        struct Main {
            fn go(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f→.either(d1→, d2→);
                ();
            }
        }
    "#,
        expect_test::expect![[r#"
        the rule "call" at (expressions.rs) failed because
          dangling borrow: @ fresh(1) has no mut-based tail in RedChain { links: [ShareDead(@ fresh(1))] }"#]]
    );
}

/// Mixed: shared[x, y] where x is place sharing (ok) but y is given (dangles).
/// Must be conservative — the Or would have a dangling branch.
#[test]
fn dangling_borrow_ref_mixed_ref_and_given() {
    crate::assert_err!(
        r#"
        struct Data {}
        struct Funcs {
            fn either[perm P](given self, x: P Data, y: given Data) → shared[x, y] Data
            where P is shared
            {
                x.share;
            }
        }
        struct Main {
            fn go(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f→.either[shared[d1]](d1.share, d2→);
                ();
            }
        }
    "#,
        expect_test::expect![[r#"
        the rule "call" at (expressions.rs) failed because
          dangling borrow: @ fresh(2) has no mut-based tail in RedChain { links: [ShareDead(@ fresh(2))] }"#]]
    );
}

/// fn foo[perm P](x: P Data) → shared[x] Data
/// Called with place sharing arg → borrow chains through, result is valid.
#[test]
fn perm_dependent_borrow_ref_arg_ok() {
    crate::assert_interpret!(
        r#"
        struct Data { n: Int; }
        struct Funcs {
            fn foo[perm P](given self, x: P Data) → shared[x] Data
            {
                x.share;
            }
        }
        struct Main {
            fn main(given self) {
                let d = new Data(42);
                let f = new Funcs();
                let result = f→.foo[shared[d]](d.share);
                print(result.n→);
                ();
            }
        }
    "#,
        expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d = new Data (42) ;
        Output: Trace:   _1_d = Data { n: 42 }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_result = _1_f → . foo [shared [_1_d]] (_1_d . share) ;
        Output: Trace:   enter Funcs.foo
        Output: Trace:     _2_x . share ;
        Output: Trace:   exit Funcs.foo => shared [_1_d] Data { n: 42 }
        Output: Trace:   _1_result = shared [_1_d] Data { n: 42 }
        Output: Trace:   print(_1_result . n →) ;
        Output: ----->   42
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]
    );
}

/// fn foo[perm P](x: P Data) → shared[x] Data
/// Called with given arg → dangling borrow. The place sharing borrows from an
/// owned value that will be dropped when the method's fresh temp is popped.
#[test]
fn perm_dependent_borrow_given_arg_dangles() {
    crate::assert_err!(
        r#"
        struct Data { n: Int; }
        struct Funcs {
            fn foo[perm P](given self, x: P Data) → shared[x] Data
            {
                x.share;
            }
        }
        struct Main {
            fn main(given self) {
                let d = new Data(42);
                let f = new Funcs();
                let result = f→.foo[given](d→);
                print(result.n→);
                ();
            }
        }
    "#,
        expect_test::expect![[r#"
        the rule "call" at (expressions.rs) failed because
          dangling borrow: @ fresh(1) has no mut-based tail in RedChain { links: [ShareDead(@ fresh(1))] }"#]]
    );
}

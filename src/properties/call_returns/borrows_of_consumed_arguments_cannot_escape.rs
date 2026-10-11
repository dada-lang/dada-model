//! ## Borrows of consumed arguments cannot escape a call
//!
//! A call cannot return a borrow whose referent is a uniquely owned argument
//! destroyed when the call returns. For an ordinary non-shared `Data`, passing
//! `d.give` to a parameter `x: given Data` does not permit the call to return
//! `ref[x] Data`. The caller's former ownership of `d` does not keep that consumed
//! argument alive.
//!
//! Every possible referent in the return permission must survive. A return type
//! `ref[x, y] Data` is rejected when either argument is consumed in this way,
//! even when the method body returns only a borrow of the other argument.
//!
//! The contrasting case passes `d.ref` to the same generic method. The returned
//! borrow can then refer to `d`, which remains in the caller, instead of depending
//! on the temporary parameter binding. Merely naming a parameter in the return
//! permission does not make its borrow invalid.
//!
//! ### Evidence and scope
//!
//! Complete Dada programs check a consumed receiver, a named argument, two
//! consumed arguments, and one borrowed argument paired with a consumed one.
//! A positive/negative pair uses the identical generic method returning `ref[x]`
//! and changes its argument from `d.ref` to `d.give` (and the corresponding
//! permission argument). Both programs attempt to read the result's integer field
//! with `print(result.n.give)`; the borrowed-argument program type-checks and
//! executes, printing `42`, while the given-argument program is rejected at the
//! call. The other rejected calls
//! report dangling borrows even when their results are unused.
//!
//! This property concerns static rejection of borrows of destroyed `given`
//! arguments. It does not claim that references to all owned values must be
//! rejected: shared ownership can survive independently. The evidence uses
//! ordinary non-shared classes. Execution of the valid control does not prove
//! general runtime destruction behavior or cover every permission composition.

use formality_core::test;

/// Method returns ref[self] where self is given → dangling borrow.
/// The ref borrows from an owned value that will be dropped when the method returns.
#[test]
fn dangling_borrow_ref_from_given_self() {
    crate::assert_err!({
        class Data {}
        class Container {
            d: given Data;
            fn get(given self) -> ref[self] Data {
                self.d.ref;
            }
        }
        class Main {
            fn go(given self) {
                let c = new Container(new Data());
                let result = c.give.get();
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "call" at (expressions.rs) failed because
          dangling borrow: @ fresh(0) has no mut-based tail in RedChain { links: [Rfd(@ fresh(0))] }"#]]);
}

/// Method returns ref[x] where x is a given parameter → dangling borrow.
#[test]
fn dangling_borrow_ref_from_given_param() {
    crate::assert_err!({
        class Data {}
        class Funcs {
            fn borrow(given self, x: given Data) -> ref[x] Data {
                x.ref;
            }
        }
        class Main {
            fn go(given self) {
                let d = new Data();
                let f = new Funcs();
                let result = f.give.borrow(d.give);
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "call" at (expressions.rs) failed because
          dangling borrow: @ fresh(1) has no mut-based tail in RedChain { links: [Rfd(@ fresh(1))] }"#]]);
}

/// Multi-place ref[x, y] where both x and y are given → dangling borrow.
/// Both branches dangle — must be an error.
#[test]
fn dangling_borrow_ref_from_two_given_params() {
    crate::assert_err!({
        class Data {}
        class Funcs {
            fn either(given self, x: given Data, y: given Data) -> ref[x, y] Data {
                x.ref;
            }
        }
        class Main {
            fn go(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.either(d1.give, d2.give);
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "call" at (expressions.rs) failed because
          dangling borrow: @ fresh(1) has no mut-based tail in RedChain { links: [Rfd(@ fresh(1))] }"#]]);
}

/// Mixed: ref[x, y] where x is ref (ok) but y is given (dangles).
/// Must be conservative — the Or would have a dangling branch.
#[test]
fn dangling_borrow_ref_mixed_ref_and_given() {
    crate::assert_err!({
        class Data {}
        class Funcs {
            fn either[perm P](given self, x: P Data, y: given Data) -> ref[x, y] Data
            where P is shared
            {
                x.ref;
            }
        }
        class Main {
            fn go(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.either[ref[d1]](d1.ref, d2.give);
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "call" at (expressions.rs) failed because
          dangling borrow: @ fresh(2) has no mut-based tail in RedChain { links: [Rfd(@ fresh(2))] }"#]]);
}

/// fn foo[perm P](x: P Data) -> ref[x] Data
/// Called with ref arg → borrow chains through, result is valid.
#[test]
fn perm_dependent_borrow_ref_arg_ok() {
    crate::assert_interpret!({
        class Data { n: Int; }
        class Funcs {
            fn foo[perm P](given self, x: P Data) -> ref[x] Data
            {
                x.ref;
            }
        }
        class Main {
            fn main(given self) {
                let d = new Data(42);
                let f = new Funcs();
                let result = f.give.foo[ref[d]](d.ref);
                print(result.n.give);
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d = new Data (42) ;
        Output: Trace:   _1_d = Data { n: 42 }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_result = _1_f . give . foo [ref [_1_d]] (_1_d . ref) ;
        Output: Trace:   enter Funcs.foo
        Output: Trace:     _2_x . ref ;
        Output: Trace:   exit Funcs.foo => ref [_1_d] Data { n: 42 }
        Output: Trace:   _1_result = ref [_1_d] Data { n: 42 }
        Output: Trace:   print(_1_result . n . give) ;
        Output: ----->   42
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

/// fn foo[perm P](x: P Data) -> ref[x] Data
/// Called with given arg → dangling borrow. The ref borrows from an
/// owned value that will be dropped when the method's fresh temp is popped.
#[test]
fn perm_dependent_borrow_given_arg_dangles() {
    crate::assert_err!({
        class Data { n: Int; }
        class Funcs {
            fn foo[perm P](given self, x: P Data) -> ref[x] Data
            {
                x.ref;
            }
        }
        class Main {
            fn main(given self) {
                let d = new Data(42);
                let f = new Funcs();
                let result = f.give.foo[given](d.give);
                print(result.n.give);
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "call" at (expressions.rs) failed because
          dangling borrow: @ fresh(1) has no mut-based tail in RedChain { links: [Rfd(@ fresh(1))] }"#]]);
}

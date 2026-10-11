//! ## Ownership can escape a call
//!
//! A method declaring `-> given Data` can return `x.give` from a parameter
//! `x: given Data`, or `self.give` from a `given self` receiver. The caller can
//! then pass the returned value to a method requiring `given Data`: ownership
//! survives the disappearance of the parameter binding. With two given
//! parameters, either can supply the owned result.
//!
//! Ownership can also escape when the declared return permission names a
//! parameter: `given_from[x]` resolves to `given` when `x` receives a `given`
//! argument. An explicit `given` return promises ownership directly; it need
//! not name which parameter supplied the value.
//!
//! The same applies to `given_from[self]` and to `given_from[x, y]` when both
//! arguments are `given`. A receiver named `self` in the caller does not change
//! which binding the callee's return permission denotes, even when the caller's
//! receiver is borrowed.
//!
//! ### Evidence and scope
//!
//! Complete Dada programs with explicit `given` returns move a named argument,
//! the receiver itself, or the first or second of two given arguments into the
//! result. The two-argument cases use separate methods with fixed choices; they
//! do not test branch-dependent moves. Consumer calls check that each returned
//! value is usable as `given` after the call, then execute that transfer.
//!
//! The `given_from` examples cover a receiver, a named argument, and two possible
//! given origins. Their receiver examples create a fresh result with the
//! receiver's permission; their named-argument examples return the argument
//! itself. Field reads print `42` after the call; separate consumer calls check
//! that the result satisfies `given`.
//!
//! Every program is type-checked and interpreted from `Main.main`. Snapshots
//! check the executed calls, printed field values where present, successful
//! completion, and an empty final heap. The borrowed-caller example invokes a
//! generic shared receiver with `ref[caller]`, so it exercises the call from an
//! actual borrowed receiver.
//!
//! These tests cover ordinary non-shared classes and `given` arguments. They
//! provide static and runtime evidence for these programs, not a preservation
//! theorem or coverage of every owned permission, type, or cleanup path.

use formality_core::test;

#[test]
fn explicit_given_return_of_named_parameter() {
    crate::assert_interpret!({
        class Data {}
        class Funcs {
            fn take(given self, x: given Data) -> given Data {
                x.give;
            }
        }
        class Sink {
            fn consume(given self, d: given Data) { (); }
        }
        class Main {
            fn main(given self) {
                let d = new Data();
                let f = new Funcs();
                let result = f.give.take(d.give);
                let sink = new Sink();
                sink.give.consume(result.give);
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d = new Data () ;
        Output: Trace:   _1_d = Data {  }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_result = _1_f . give . take (_1_d . give) ;
        Output: Trace:   enter Funcs.take
        Output: Trace:     _2_x . give ;
        Output: Trace:   exit Funcs.take => Data {  }
        Output: Trace:   _1_result = Data {  }
        Output: Trace:   let _1_sink = new Sink () ;
        Output: Trace:   _1_sink = Sink {  }
        Output: Trace:   _1_sink . give . consume (_1_result . give) ;
        Output: Trace:   enter Sink.consume
        Output: Trace:     () ;
        Output: Trace:   exit Sink.consume => ()
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

#[test]
fn explicit_given_return_of_receiver() {
    crate::assert_interpret!({
        class Data {
            fn take(given self) -> given Data {
                self.give;
            }
        }
        class Sink {
            fn consume(given self, d: given Data) { (); }
        }
        class Main {
            fn main(given self) {
                let d = new Data();
                let result = d.give.take();
                let sink = new Sink();
                sink.give.consume(result.give);
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d = new Data () ;
        Output: Trace:   _1_d = Data {  }
        Output: Trace:   let _1_result = _1_d . give . take () ;
        Output: Trace:   enter Data.take
        Output: Trace:     _2_self . give ;
        Output: Trace:   exit Data.take => Data {  }
        Output: Trace:   _1_result = Data {  }
        Output: Trace:   let _1_sink = new Sink () ;
        Output: Trace:   _1_sink = Sink {  }
        Output: Trace:   _1_sink . give . consume (_1_result . give) ;
        Output: Trace:   enter Sink.consume
        Output: Trace:     () ;
        Output: Trace:   exit Sink.consume => ()
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

#[test]
fn explicit_given_return_of_first_parameter() {
    crate::assert_interpret!({
        class Data {}
        class Funcs {
            fn pick(given self, x: given Data, y: given Data) -> given Data {
                x.give;
            }
        }
        class Sink {
            fn consume(given self, d: given Data) { (); }
        }
        class Main {
            fn main(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.pick(d1.give, d2.give);
                let sink = new Sink();
                sink.give.consume(result.give);
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
        Output: Trace:   let _1_result = _1_f . give . pick (_1_d1 . give, _1_d2 . give) ;
        Output: Trace:   enter Funcs.pick
        Output: Trace:     _2_x . give ;
        Output: Trace:   exit Funcs.pick => Data {  }
        Output: Trace:   _1_result = Data {  }
        Output: Trace:   let _1_sink = new Sink () ;
        Output: Trace:   _1_sink = Sink {  }
        Output: Trace:   _1_sink . give . consume (_1_result . give) ;
        Output: Trace:   enter Sink.consume
        Output: Trace:     () ;
        Output: Trace:   exit Sink.consume => ()
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

#[test]
fn explicit_given_return_of_second_parameter() {
    crate::assert_interpret!({
        class Data {}
        class Funcs {
            fn pick(given self, x: given Data, y: given Data) -> given Data {
                y.give;
            }
        }
        class Sink {
            fn consume(given self, d: given Data) { (); }
        }
        class Main {
            fn main(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.pick(d1.give, d2.give);
                let sink = new Sink();
                sink.give.consume(result.give);
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
        Output: Trace:   let _1_result = _1_f . give . pick (_1_d1 . give, _1_d2 . give) ;
        Output: Trace:   enter Funcs.pick
        Output: Trace:     _2_y . give ;
        Output: Trace:   exit Funcs.pick => Data {  }
        Output: Trace:   _1_result = Data {  }
        Output: Trace:   let _1_sink = new Sink () ;
        Output: Trace:   _1_sink = Sink {  }
        Output: Trace:   _1_sink . give . consume (_1_result . give) ;
        Output: Trace:   enter Sink.consume
        Output: Trace:     () ;
        Output: Trace:   exit Sink.consume => ()
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

/// Basic: method returns given_from[self] with given self.
/// Resolves ownership from the callee receiver.
#[test]
fn given_from_self_basic() {
    crate::assert_interpret!({
        class Data { n: Int; }
        class Container {
            fn get(given self) -> given_from[self] Data {
                new Data(42);
            }
        }
        class Main {
            fn main(given self) {
                let c = new Container();
                let result = c.give.get();
                print(result.n.give);
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_c = new Container () ;
        Output: Trace:   _1_c = Container {  }
        Output: Trace:   let _1_result = _1_c . give . get () ;
        Output: Trace:   enter Container.get
        Output: Trace:     new Data (42) ;
        Output: Trace:   exit Container.get => Data { n: 42 }
        Output: Trace:   _1_result = Data { n: 42 }
        Output: Trace:   print(_1_result . n . give) ;
        Output: ----->   42
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

/// The caller's self is instantiated with ref permission, but the callee's self is given.
/// The return type given_from[self] resolves from Container's given self,
/// independently of Caller's ref self.
///
/// After the call, `result` should be `given Data`, so giving it away should work.
#[test]
fn given_from_self_different_caller_perm() {
    crate::assert_interpret!({
        class Data {}
        class Container {
            fn get(given self) -> given_from[self] Data {
                new Data();
            }
        }
        class Sink {
            fn consume(given self, d: given Data) {
                ();
            }
        }
        class Caller {
            fn go[perm P](P self, c: given Container)
            where P is shared
            {
                let result = c.give.get();
                let sink = new Sink();
                sink.give.consume(result.give);
                ();
            }
        }
        class Main {
            fn main(given self) {
                let caller = new Caller();
                let c = new Container();
                caller.ref.go[ref[caller]](c.give);
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_caller = new Caller () ;
        Output: Trace:   _1_caller = Caller {  }
        Output: Trace:   let _1_c = new Container () ;
        Output: Trace:   _1_c = Container {  }
        Output: Trace:   _1_caller . ref . go [ref [_1_caller]] (_1_c . give) ;
        Output: Trace:   enter Caller.go
        Output: Trace:     let _2_result = _2_c . give . get () ;
        Output: Trace:     enter Container.get
        Output: Trace:       new Data () ;
        Output: Trace:     exit Container.get => Data {  }
        Output: Trace:     _2_result = Data {  }
        Output: Trace:     let _2_sink = new Sink () ;
        Output: Trace:     _2_sink = Sink {  }
        Output: Trace:     _2_sink . give . consume (_2_result . give) ;
        Output: Trace:     enter Sink.consume
        Output: Trace:       () ;
        Output: Trace:     exit Sink.consume => ()
        Output: Trace:     () ;
        Output: Trace:   exit Caller.go => ()
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

/// Named parameter: method returns given_from[x] where x is a named parameter.
/// The return type should resolve based on x's binding at the call site.
#[test]
fn given_from_named_param() {
    crate::assert_interpret!({
        class Data { n: Int; }
        class Funcs {
            fn take(given self, x: given Data) -> given_from[x] Data {
                x.give;
            }
        }
        class Main {
            fn main(given self) {
                let d = new Data(42);
                let f = new Funcs();
                let result = f.give.take(d.give);
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
        Output: Trace:   let _1_result = _1_f . give . take (_1_d . give) ;
        Output: Trace:   enter Funcs.take
        Output: Trace:     _2_x . give ;
        Output: Trace:   exit Funcs.take => Data { n: 42 }
        Output: Trace:   _1_result = Data { n: 42 }
        Output: Trace:   print(_1_result . n . give) ;
        Output: ----->   42
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

/// Named parameter given_from resolution: result should be given, so
/// giving it to a consumer should work.
#[test]
fn given_from_named_param_give_result() {
    crate::assert_interpret!({
        class Data {}
        class Funcs {
            fn take(given self, x: given Data) -> given_from[x] Data {
                x.give;
            }
        }
        class Sink {
            fn consume(given self, d: given Data) {
                ();
            }
        }
        class Main {
            fn main(given self) {
                let d = new Data();
                let f = new Funcs();
                let result = f.give.take(d.give);
                let sink = new Sink();
                sink.give.consume(result.give);
                ();
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d = new Data () ;
        Output: Trace:   _1_d = Data {  }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_result = _1_f . give . take (_1_d . give) ;
        Output: Trace:   enter Funcs.take
        Output: Trace:     _2_x . give ;
        Output: Trace:   exit Funcs.take => Data {  }
        Output: Trace:   _1_result = Data {  }
        Output: Trace:   let _1_sink = new Sink () ;
        Output: Trace:   _1_sink = Sink {  }
        Output: Trace:   _1_sink . give . consume (_1_result . give) ;
        Output: Trace:   enter Sink.consume
        Output: Trace:     () ;
        Output: Trace:   exit Sink.consume => ()
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

/// given_from[x, y] with both given args → produces or(given, given) = given.
/// Result should be fully owned.
#[test]
fn multi_place_given_from_both_given() {
    crate::assert_interpret!({
        class Data {}
        class Funcs {
            fn pick(given self, x: given Data, y: given Data) -> given_from[x, y] Data {
                x.give;
            }
        }
        class Sink {
            fn consume(given self, d: given Data) {
                ();
            }
        }
        class Main {
            fn main(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.pick(d1.give, d2.give);
                let sink = new Sink();
                sink.give.consume(result.give);
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
        Output: Trace:   let _1_result = _1_f . give . pick (_1_d1 . give, _1_d2 . give) ;
        Output: Trace:   enter Funcs.pick
        Output: Trace:     _2_x . give ;
        Output: Trace:   exit Funcs.pick => Data {  }
        Output: Trace:   _1_result = Data {  }
        Output: Trace:   let _1_sink = new Sink () ;
        Output: Trace:   _1_sink = Sink {  }
        Output: Trace:   _1_sink . give . consume (_1_result . give) ;
        Output: Trace:   enter Sink.consume
        Output: Trace:     () ;
        Output: Trace:   exit Sink.consume => ()
        Output: Trace:   () ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

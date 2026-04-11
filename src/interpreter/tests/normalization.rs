// Interpreter tests for normalization at method-call boundaries.
//
// These correspond to the type system tests in normalization.rs but verify
// runtime values, permissions, and heap state.
//
// Current state (after Phase 3b):
// - The type binding injection workaround is removed from `call_method`.
// - A preservation assertion (`check_type` on result types) catches any
//   method-scoped variables leaking into the caller's env.
// - Tests where result types reference method-scoped variables are #[ignore]'d
//   until Phase 3c adds `normalize_ty_for_pop` to the interpreter.
// - Tests where result types are "clean" (e.g., `new Data(42)` returns plain
//   `Data`, or `given[self]` with `given self` resolves to plain type)
//   pass without normalization.
//
// After Phase 3c, we expect:
// - `normalize_ty_for_pop` is called on result types in the interpreter
// - All #[ignore]'d tests are un-ignored and pass
// - Trace output for result types will show normalized permissions
//   (e.g., `ref[_1_d] Data` instead of `ref[_2_x] ref[_1_d] Data`,
//    `or(mut[d1], mut[d2]) Data` instead of `mut[_2_x] mut[d1] Data`)

// ---------------------------------------------------------------------------
// given[self] resolution: basic ownership transfer
// ---------------------------------------------------------------------------

/// Method returns given[self] Data — after normalization, the result
/// should have `given Data` type (owned), not a dangling reference to the
/// method's self variable.
#[test]
fn interp_given_self_basic() {
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Container {
                fn get(given self) -> given[self] Data {
                    new Data(42);
                }
            }
            class Main {
                fn main(given self) -> Data {
                    let c = new Container();
                    c.give.get();
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_c = new Container () ;
            Output: Trace:   _1_c = Container {  }
            Output: Trace:   _1_c . give . get () ;
            Output: Trace:   enter Container.get
            Output: Trace:     new Data (42) ;
            Output: Trace:   exit Container.get => Data { x: 42 }
            Output: Trace: exit Main.main => Data { x: 42 }
            Result: Ok: Data { x: 42 }
            Alloc 0x07: [Int(42)]"#]])
    );
}

/// given[self] where the method's self is given but the caller
/// subsequently gives the result to a consumer. The result should be
/// `given Data` (from Container's given self).
///
/// This works even without normalization because the interpreter builds
/// result types from the runtime value (new Data(99) → type `Data`), not
/// from the declared return type. The given[self] annotation is checked
/// by the type system but doesn't affect the interpreter's type tracking here.
#[test]
fn interp_given_self_give_to_consumer() {
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Container {
                fn get(given self) -> given[self] Data {
                    new Data(99);
                }
            }
            class Sink {
                fn consume(given self, d: given Data) -> Int {
                    d.x.give;
                }
            }
            class Main {
                fn main(given self) -> Int {
                    let c = new Container();
                    let result = c.give.get();
                    let sink = new Sink();
                    sink.give.consume(result.give);
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_c = new Container () ;
            Output: Trace:   _1_c = Container {  }
            Output: Trace:   let _1_result = _1_c . give . get () ;
            Output: Trace:   enter Container.get
            Output: Trace:     new Data (99) ;
            Output: Trace:   exit Container.get => Data { x: 99 }
            Output: Trace:   _1_result = Data { x: 99 }
            Output: Trace:   let _1_sink = new Sink () ;
            Output: Trace:   _1_sink = Sink {  }
            Output: Trace:   _1_sink . give . consume (_1_result . give) ;
            Output: Trace:   enter Sink.consume
            Output: Trace:     _3_d . x . give ;
            Output: Trace:   exit Sink.consume => 99
            Output: Trace: exit Main.main => 99
            Result: Ok: 99
            Alloc 0x0e: [Int(99)]"#]])
    );
}

/// Method returns a field through a place reference (self.d.ref → ref[_N_self] Data).
/// Without normalization, the result type contains the method-scoped variable
/// `_N_self`, which violates preservation. After Phase 3c, normalization resolves
/// this to a caller-scoped permission.
#[test]
fn interp_ref_self_field_preservation() {
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Container {
                d: given Data;
                fn get_ref[perm P](P self) -> ref[self] Data
                where P is copy
                {
                    self.d.ref;
                }
            }
            class Main {
                fn main(given self) -> Int {
                    let c = new Container(new Data(77));
                    let result = c.ref.get_ref[ref[c]]();
                    result.x.give;
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_c = new Container (new Data (77)) ;
            Output: Trace:   _1_c = Container { d: Data { x: 77 } }
            Output: Trace:   let _1_result = _1_c . ref . get_ref [ref [_1_c]] () ;
            Output: Trace:   enter Container.get_ref
            Output: Trace:     _2_self . d . ref ;
            Output: Trace:   exit Container.get_ref => ref [_1_c] Data { x: 77 }
            Output: Trace:   _1_result = ref [_1_c] Data { x: 77 }
            Output: Trace:   _1_result . x . give ;
            Output: Trace: exit Main.main => 77
            Result: Ok: 77
            Alloc 0x0a: [Int(77)]"#]])
    );
}

// ---------------------------------------------------------------------------
// given[x] with named parameter
// ---------------------------------------------------------------------------

/// Method returns given[x] where x is a named parameter passed as given.
/// After normalization, result should be `given Data`.
#[test]
fn interp_given_named_param() {
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Funcs {
                fn take(given self, x: given Data) -> given[x] Data {
                    x.give;
                }
            }
            class Main {
                fn main(given self) -> Data {
                    let d = new Data(7);
                    let f = new Funcs();
                    f.give.take(d.give);
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (7) ;
            Output: Trace:   _1_d = Data { x: 7 }
            Output: Trace:   let _1_f = new Funcs () ;
            Output: Trace:   _1_f = Funcs {  }
            Output: Trace:   _1_f . give . take (_1_d . give) ;
            Output: Trace:   enter Funcs.take
            Output: Trace:     _2_x . give ;
            Output: Trace:   exit Funcs.take => Data { x: 7 }
            Output: Trace: exit Main.main => Data { x: 7 }
            Result: Ok: Data { x: 7 }
            Alloc 0x0a: [Int(7)]"#]])
    );
}

/// given[x] result can be given away (proves it's owned).
#[test]
fn interp_given_named_param_give_result() {
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Funcs {
                fn take(given self, x: given Data) -> given[x] Data {
                    x.give;
                }
            }
            class Sink {
                fn consume(given self, d: given Data) -> Int {
                    d.x.give;
                }
            }
            class Main {
                fn main(given self) -> Int {
                    let d = new Data(55);
                    let f = new Funcs();
                    let result = f.give.take(d.give);
                    let sink = new Sink();
                    sink.give.consume(result.give);
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (55) ;
            Output: Trace:   _1_d = Data { x: 55 }
            Output: Trace:   let _1_f = new Funcs () ;
            Output: Trace:   _1_f = Funcs {  }
            Output: Trace:   let _1_result = _1_f . give . take (_1_d . give) ;
            Output: Trace:   enter Funcs.take
            Output: Trace:     _2_x . give ;
            Output: Trace:   exit Funcs.take => Data { x: 55 }
            Output: Trace:   _1_result = Data { x: 55 }
            Output: Trace:   let _1_sink = new Sink () ;
            Output: Trace:   _1_sink = Sink {  }
            Output: Trace:   _1_sink . give . consume (_1_result . give) ;
            Output: Trace:   enter Sink.consume
            Output: Trace:     _3_d . x . give ;
            Output: Trace:   exit Sink.consume => 55
            Output: Trace: exit Main.main => 55
            Result: Ok: 55
            Alloc 0x11: [Int(55)]"#]])
    );
}

// ---------------------------------------------------------------------------
// Borrow chaining: ref through ref
// ---------------------------------------------------------------------------

/// Method returns ref[x] where x is a ref parameter → borrow chains through.
/// The result should be readable in the caller's scope.
///
/// Currently hits preservation violation: result type `ref[_2_x] ref[_1_d] Data`
/// references method-scoped `_2_x`. After Phase 3c normalization, this resolves
/// to `ref[_1_d] Data` (copy tail drops the dead link).
#[test]
fn interp_borrow_chain_ref_through_ref() {
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Funcs {
                fn borrow[perm P](given self, x: P Data) -> ref[x] Data
                where P is copy
                {
                    x.ref;
                }
            }
            class Main {
                fn main(given self) -> Int {
                    let d = new Data(33);
                    let f = new Funcs();
                    let result = f.give.borrow[ref[d]](d.ref);
                    result.x.give;
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d = new Data (33) ;
            Output: Trace:   _1_d = Data { x: 33 }
            Output: Trace:   let _1_f = new Funcs () ;
            Output: Trace:   _1_f = Funcs {  }
            Output: Trace:   let _1_result = _1_f . give . borrow [ref [_1_d]] (_1_d . ref) ;
            Output: Trace:   enter Funcs.borrow
            Output: Trace:     _2_x . ref ;
            Output: Trace:   exit Funcs.borrow => ref [_1_d] Data { x: 33 }
            Output: Trace:   _1_result = ref [_1_d] Data { x: 33 }
            Output: Trace:   _1_result . x . give ;
            Output: Trace: exit Main.main => 33
            Result: Ok: 33
            Alloc 0x0c: [Int(33)]"#]])
    );
}

/// ref[self] where self is ref → borrow chains through, field readable.
///
/// Currently hits preservation violation: result type references method-scoped
/// `_2_self`. After Phase 3c normalization, resolves to `ref[_1_c] Data`.
#[test]
fn interp_borrow_chain_ref_through_ref_self() {
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Container {
                d: given Data;
                fn get[perm P](P self) -> ref[self] Data
                where P is copy
                {
                    self.d.ref;
                }
            }
            class Main {
                fn main(given self) -> Int {
                    let c = new Container(new Data(44));
                    let result = c.ref.get[ref[c]]();
                    result.x.give;
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_c = new Container (new Data (44)) ;
            Output: Trace:   _1_c = Container { d: Data { x: 44 } }
            Output: Trace:   let _1_result = _1_c . ref . get [ref [_1_c]] () ;
            Output: Trace:   enter Container.get
            Output: Trace:     _2_self . d . ref ;
            Output: Trace:   exit Container.get => ref [_1_c] Data { x: 44 }
            Output: Trace:   _1_result = ref [_1_c] Data { x: 44 }
            Output: Trace:   _1_result . x . give ;
            Output: Trace: exit Main.main => 44
            Result: Ok: 44
            Alloc 0x0a: [Int(44)]"#]])
    );
}

// ---------------------------------------------------------------------------
// Multi-place resolution producing Or
// ---------------------------------------------------------------------------

/// ref[x, y] with different ref args → result has or(ref[d1], ref[d2]) perm.
/// Reading a field from the result should work.
///
/// Currently hits preservation violation: result type references method-scoped
/// `_2_x`. After Phase 3c normalization, resolves to `or(ref[_1_d1], ref[_1_d2]) Data`.
#[test]
fn interp_multi_place_ref_produces_or() {
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Funcs {
                fn either[perm P, perm Q](given self, x: P Data, y: Q Data) -> ref[x, y] Data
                where P is copy, Q is copy
                {
                    x.ref;
                }
            }
            class Main {
                fn main(given self) -> Int {
                    let d1 = new Data(10);
                    let d2 = new Data(20);
                    let f = new Funcs();
                    let result = f.give.either[ref[d1], ref[d2]](d1.ref, d2.ref);
                    result.x.give;
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d1 = new Data (10) ;
            Output: Trace:   _1_d1 = Data { x: 10 }
            Output: Trace:   let _1_d2 = new Data (20) ;
            Output: Trace:   _1_d2 = Data { x: 20 }
            Output: Trace:   let _1_f = new Funcs () ;
            Output: Trace:   _1_f = Funcs {  }
            Output: Trace:   let _1_result = _1_f . give . either [ref [_1_d1], ref [_1_d2]] (_1_d1 . ref, _1_d2 . ref) ;
            Output: Trace:   enter Funcs.either
            Output: Trace:     _2_x . ref ;
            Output: Trace:   exit Funcs.either => ref [_1_d1] Data { x: 10 }
            Output: Trace:   _1_result = ref [_1_d1] Data { x: 10 }
            Output: Trace:   _1_result . x . give ;
            Output: Trace: exit Main.main => 10
            Result: Ok: 10
            Alloc 0x10: [Int(10)]"#]])
    );
}

/// given[x, y] with both given → result is given (or(given, given) = given).
/// Can give result away.
#[test]
fn interp_multi_place_given_both_given() {
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Funcs {
                fn pick(given self, x: given Data, y: given Data) -> given[x, y] Data {
                    x.give;
                }
            }
            class Sink {
                fn consume(given self, d: given Data) -> Int {
                    d.x.give;
                }
            }
            class Main {
                fn main(given self) -> Int {
                    let d1 = new Data(100);
                    let d2 = new Data(200);
                    let f = new Funcs();
                    let result = f.give.pick(d1.give, d2.give);
                    let sink = new Sink();
                    sink.give.consume(result.give);
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d1 = new Data (100) ;
            Output: Trace:   _1_d1 = Data { x: 100 }
            Output: Trace:   let _1_d2 = new Data (200) ;
            Output: Trace:   _1_d2 = Data { x: 200 }
            Output: Trace:   let _1_f = new Funcs () ;
            Output: Trace:   _1_f = Funcs {  }
            Output: Trace:   let _1_result = _1_f . give . pick (_1_d1 . give, _1_d2 . give) ;
            Output: Trace:   enter Funcs.pick
            Output: Trace:     _2_x . give ;
            Output: Trace:   exit Funcs.pick => Data { x: 100 }
            Output: Trace:   _1_result = Data { x: 100 }
            Output: Trace:   let _1_sink = new Sink () ;
            Output: Trace:   _1_sink = Sink {  }
            Output: Trace:   _1_sink . give . consume (_1_result . give) ;
            Output: Trace:   enter Sink.consume
            Output: Trace:     _3_d . x . give ;
            Output: Trace:   exit Sink.consume => 100
            Output: Trace: exit Main.main => 100
            Result: Ok: 100
            Alloc 0x15: [Int(100)]"#]])
    );
}

/// mut[x, y] through mut → result has or(mut[d1], mut[d2]).
/// Mutating through the result should work.
///
/// Currently hits preservation violation: result type `mut[_2_x] mut[_1_d1] Data`
/// references method-scoped `_2_x`. After Phase 3c normalization, resolves to
/// `or(mut[_1_d1], mut[_1_d2]) Data`.
#[test]
fn interp_multi_place_mut_through_mut() {
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Funcs {
                fn either[perm P, perm Q](given self, x: P Data, y: Q Data) -> mut[x, y] Data
                where P is mut, Q is mut
                {
                    x.mut;
                }
            }
            class Main {
                fn main(given self) -> Int {
                    let d1 = new Data(10);
                    let d2 = new Data(20);
                    let f = new Funcs();
                    let result = f.give.either[mut[d1], mut[d2]](d1.mut, d2.mut);
                    result.x.give;
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_d1 = new Data (10) ;
            Output: Trace:   _1_d1 = Data { x: 10 }
            Output: Trace:   let _1_d2 = new Data (20) ;
            Output: Trace:   _1_d2 = Data { x: 20 }
            Output: Trace:   let _1_f = new Funcs () ;
            Output: Trace:   _1_f = Funcs {  }
            Output: Trace:   let _1_result = _1_f . give . either [mut [_1_d1], mut [_1_d2]] (_1_d1 . mut, _1_d2 . mut) ;
            Output: Trace:   enter Funcs.either
            Output: Trace:     _2_x . mut ;
            Output: Trace:   exit Funcs.either => mut [_1_d1] mut [_1_d1] Data { x: 10 }
            Output: Trace:   _1_result = mut [_1_d1] mut [_1_d1] Data { x: 10 }
            Output: Trace:   _1_result . x . give ;
            Output: Trace: exit Main.main => 10
            Result: Ok: 10
            Alloc 0x10: [Int(10)]"#]])
    );
}

// ---------------------------------------------------------------------------
// Verifying workaround removal: method-scoped names should NOT leak
// ---------------------------------------------------------------------------

/// After normalization, calling two methods in sequence should not accumulate
/// leaked bindings. This test exercises that the workaround (injecting
/// method-scoped type bindings into caller env) is removed.
#[test]
fn interp_no_leaked_method_bindings() {
    crate::assert_interpret!(
        {
            class Data { x: Int; }
            class Funcs {
                fn take(given self, x: given Data) -> given[x] Data {
                    x.give;
                }
            }
            class Main {
                fn main(given self) -> Int {
                    let f1 = new Funcs();
                    let d1 = new Data(1);
                    let r1 = f1.give.take(d1.give);
                    let f2 = new Funcs();
                    let d2 = new Data(2);
                    let r2 = f2.give.take(d2.give);
                    r1.x.give + r2.x.give;
                }
            }
        },
         type: ok, interpret: ok(expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_f1 = new Funcs () ;
            Output: Trace:   _1_f1 = Funcs {  }
            Output: Trace:   let _1_d1 = new Data (1) ;
            Output: Trace:   _1_d1 = Data { x: 1 }
            Output: Trace:   let _1_r1 = _1_f1 . give . take (_1_d1 . give) ;
            Output: Trace:   enter Funcs.take
            Output: Trace:     _2_x . give ;
            Output: Trace:   exit Funcs.take => Data { x: 1 }
            Output: Trace:   _1_r1 = Data { x: 1 }
            Output: Trace:   let _1_f2 = new Funcs () ;
            Output: Trace:   _1_f2 = Funcs {  }
            Output: Trace:   let _1_d2 = new Data (2) ;
            Output: Trace:   _1_d2 = Data { x: 2 }
            Output: Trace:   let _1_r2 = _1_f2 . give . take (_1_d2 . give) ;
            Output: Trace:   enter Funcs.take
            Output: Trace:     _3_x . give ;
            Output: Trace:   exit Funcs.take => Data { x: 2 }
            Output: Trace:   _1_r2 = Data { x: 2 }
            Output: Trace:   _1_r1 . x . give + _1_r2 . x . give ;
            Output: Trace: exit Main.main => 3
            Result: Ok: 3
            Alloc 0x18: [Int(3)]"#]])
    );
}

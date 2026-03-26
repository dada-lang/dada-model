use formality_core::test;

// =============================================================================
// Phase 2a: Tests for output renaming + normalization
//
// These tests exercise call-site resolution of return types that reference
// method parameters. They cover:
// - given_from[self] resolution (currently works by accident via Var::This bug)
// - given_from[self] where caller has different self permission (exposes bug)
// - Dangling borrows (ref from given — should error)
// - Borrow chaining (ref through ref — should succeed)
// - Multi-place resolution producing Or
//
// All tests should fail until Phase 2b lands.
// =============================================================================

// ---------------------------------------------------------------------------
// given_from[self] resolution
// ---------------------------------------------------------------------------

/// Basic: method returns given_from[self] with given self.
/// Currently passes by accident (Var::This collision).
/// After fix, should still pass with correct resolution.
#[test]
fn given_from_self_basic() {
    crate::assert_ok!({
        class Data {}
        class Container {
            fn get(given self) -> given_from[self] Data {
                new Data();
            }
        }
        class Main {
            fn go(given self) {
                let c = new Container();
                let result = c.give.get();
                ();
            }
        }
    });
}

/// Bug exposer: caller's self has ref permission, but the method's self
/// is given. The return type given_from[self] should resolve to given (from
/// Container's given self), NOT ref (from Caller's ref self).
///
/// After the call, `result` should be `given Data`, so giving it away should work.
#[test]
fn given_from_self_different_caller_perm() {
    crate::assert_ok!({
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
            fn go(ref self, c: given Container) {
                let result = c.give.get();
                let sink = new Sink();
                sink.give.consume(result.give);
                ();
            }
        }
    });
}

/// Named parameter: method returns given_from[x] where x is a named parameter.
/// The return type should resolve based on x's binding at the call site.
#[test]
fn given_from_named_param() {
    crate::assert_ok!({
        class Data {}
        class Funcs {
            fn take(given self, x: given Data) -> given_from[x] Data {
                x.give;
            }
        }
        class Main {
            fn go(given self) {
                let d = new Data();
                let f = new Funcs();
                let result = f.give.take(d.give);
                ();
            }
        }
    });
}

/// Named parameter given_from resolution: result should be given, so
/// giving it to a consumer should work.
#[test]
fn given_from_named_param_give_result() {
    crate::assert_ok!({
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
            fn go(given self) {
                let d = new Data();
                let f = new Funcs();
                let result = f.give.take(d.give);
                let sink = new Sink();
                sink.give.consume(result.give);
                ();
            }
        }
    });
}

// ---------------------------------------------------------------------------
// Dangling borrows (should error)
// ---------------------------------------------------------------------------

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
    }, expect_test::expect![[""]]);
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
    }, expect_test::expect![[""]]);
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
    }, expect_test::expect![[""]]);
}

/// Mixed: ref[x, y] where x is ref (ok) but y is given (dangles).
/// Must be conservative — the Or would have a dangling branch.
#[test]
fn dangling_borrow_ref_mixed_ref_and_given() {
    crate::assert_err!({
        class Data {}
        class Funcs {
            fn either[perm P](given self, x: P Data, y: given Data) -> ref[x, y] Data
            where P is copy
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
    }, expect_test::expect![[""]]);
}

// ---------------------------------------------------------------------------
// Borrow chaining (should succeed)
// ---------------------------------------------------------------------------

/// Method returns ref[x] where x is passed as ref → borrow chains through.
/// Result should be ref[d] in the caller's scope.
#[test]
fn borrow_chain_ref_through_ref() {
    crate::assert_ok!({
        class Data {}
        class Funcs {
            fn borrow[perm P](given self, x: P Data) -> ref[x] Data
            where P is copy
            {
                x.ref;
            }
        }
        class Main {
            fn go(given self) {
                let d = new Data();
                let f = new Funcs();
                let result = f.give.borrow[ref[d]](d.ref);
                ();
            }
        }
    });
}

/// Method returns ref[self] where self is passed as ref → borrow chains.
#[test]
fn borrow_chain_ref_through_ref_self() {
    crate::assert_ok!({
        class Data {}
        class Container {
            d: given Data;
            fn get[perm P](P self) -> ref[self] Data
            where P is copy
            {
                self.d.ref;
            }
        }
        class Main {
            fn go(given self) {
                let c = new Container(new Data());
                let result = c.ref.get[ref[c]]();
                ();
            }
        }
    });
}

// ---------------------------------------------------------------------------
// Multi-place resolution producing Or
// ---------------------------------------------------------------------------

/// ref[x, y] with different ref args → produces or(ref[d1], ref[d2]).
/// The result should be usable as ref[d1, d2] (equivalent via subtyping).
#[test]
fn multi_place_ref_produces_or() {
    crate::assert_ok!({
        class Data {}
        class Funcs {
            fn either[perm P, perm Q](given self, x: P Data, y: Q Data) -> ref[x, y] Data
            where P is copy, Q is copy
            {
                x.ref;
            }
        }
        class Main {
            fn go(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.either[ref[d1], ref[d2]](d1.ref, d2.ref);
                ();
            }
        }
    });
}

/// given_from[x, y] with both given args → produces or(given, given) = given.
/// Result should be fully owned.
#[test]
fn multi_place_given_from_both_given() {
    crate::assert_ok!({
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
            fn go(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.pick(d1.give, d2.give);
                let sink = new Sink();
                sink.give.consume(result.give);
                ();
            }
        }
    });
}

/// mut[x, y] through mut → dead-link stripping produces or(mut[a], mut[b]).
/// Both args passed as mut, return type is mut[x, y].
#[test]
fn multi_place_mut_through_mut() {
    crate::assert_ok!({
        class Data {}
        class Funcs {
            fn either[perm P, perm Q](given self, x: P Data, y: Q Data) -> mut[x, y] Data
            where P is mut, Q is mut
            {
                x.mut;
            }
        }
        class Main {
            fn go(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.either[mut[d1], mut[d2]](d1.mut, d2.mut);
                ();
            }
        }
    });
}

/// ref[x, y] through mut → dead-link stripping + Rfd→Shared weakening
/// produces or(shared mut[a], shared mut[b]).
#[test]
fn multi_place_ref_through_mut() {
    crate::assert_ok!({
        class Data {}
        class Funcs {
            fn either[perm P, perm Q](given self, x: P Data, y: Q Data) -> ref[x, y] Data
            where P is mut, Q is mut
            {
                x.ref;
            }
        }
        class Main {
            fn go(given self) {
                let d1 = new Data();
                let d2 = new Data();
                let f = new Funcs();
                let result = f.give.either[mut[d1], mut[d2]](d1.mut, d2.mut);
                ();
            }
        }
    });
}

use formality_core::test;

// =============================================================================
// Phase 4a: Tests for type system block-exit normalization
//
// These tests exercise normalization of result types when block-scoped
// variables go out of scope. The type system should pop let-bound variables
// at block exit and normalize the block's result type against them.
//
// Currently the type system never pops let-bound variables — they stay in
// the env indefinitely. These tests verify that:
// - Block-local variables are popped at block exit
// - Result types referencing block-locals are normalized
// - Dangling borrows from block-locals are detected
// =============================================================================

// ---------------------------------------------------------------------------
// given_from resolution through block-local variables
// ---------------------------------------------------------------------------

/// Block returns a value obtained via given_from[local] where local is
/// a let-bound variable inside the block. After normalization, the
/// given_from should resolve to given (ownership transferred).
#[test]
fn block_given_from_local_resolves_to_given() {
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
        class Main {
            fn go(given self) {
                let result = {
                    let c = new Container();
                    c.give.get();
                };
                let sink = new Sink();
                sink.give.consume(result.give);
                ();
            }
        }
    });
}

/// Same as above but with a named parameter: block calls a method
/// with given_from[x] return type where x is bound to a block-local value.
#[test]
fn block_given_from_local_param_resolves_to_given() {
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
                let result = {
                    let d = new Data();
                    let f = new Funcs();
                    f.give.take(d.give);
                };
                let sink = new Sink();
                sink.give.consume(result.give);
                ();
            }
        }
    });
}

// ---------------------------------------------------------------------------
// Dangling borrows from block-locals (should error)
// ---------------------------------------------------------------------------

/// Block returns ref[local] where local is an owned block-scoped variable.
/// This is a dangling borrow — the local will be dropped at block exit.
#[test]
fn block_dangling_borrow_ref_from_local() {
    crate::assert_err!({
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
                let result = {
                    let c = new Container(new Data());
                    c.ref.get[ref[c]]();
                };
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "place" at (blocks.rs) failed because
          dangling borrow: return type borrows from `c` which has `given` permission — the borrow would outlive the owned value"#]]);
}

/// Block returns mut[local] where local is an owned block-scoped variable.
/// Same dangling borrow issue.
#[test]
fn block_dangling_borrow_mut_from_local() {
    crate::assert_err!({
        class Data {}
        class Container {
            d: given Data;
            fn get_mut[perm P](P self) -> mut[self] Data
            where P is mut
            {
                self.d.mut;
            }
        }
        class Main {
            fn go(given self) {
                let result = {
                    let c = new Container(new Data());
                    c.mut.get_mut[mut[c]]();
                };
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "place" at (blocks.rs) failed because
          dangling borrow: chain `RedChain { links: [Mtd(c)] }` borrows through `c` which is being popped (type not shareable or tail not mut-based)"#]]);
}

// ---------------------------------------------------------------------------
// Borrow chaining through block-locals
// ---------------------------------------------------------------------------

/// Block-local borrows from outer variable. The ref chain goes:
/// result -> block-local -> outer variable.
/// After normalizing the block-local away, result should be ref[outer].
#[test]
fn block_borrow_chain_ref_through_local_to_outer() {
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
                let outer = new Data();
                let result = {
                    let f = new Funcs();
                    f.give.borrow[ref[outer]](outer.ref);
                };
                ();
            }
        }
    });
}

// ---------------------------------------------------------------------------
// Block-local variables should not leak into outer scope
// ---------------------------------------------------------------------------

/// After a block exits, its local variables should not be in the env.
/// This test creates a block-local and then tries to use it after the block.
/// This should fail because the variable is out of scope.
/// (This tests that variables are actually popped, not just normalization.)
#[test]
fn block_local_not_accessible_after_block() {
    crate::assert_err!({
        class Data {}
        class Main {
            fn go(given self) {
                let result = {
                    let d = new Data();
                    ();
                };
                d.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "give place" at (expressions.rs) failed because
          no variable named `d`"#]]);
}

// ---------------------------------------------------------------------------
// Nested blocks
// ---------------------------------------------------------------------------

/// Inner block's local is normalized before outer block sees it.
/// The inner block produces given Data (from given_from[inner_local]).
/// The outer block can then give it away.
#[test]
fn nested_block_given_from_inner_local() {
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
        class Main {
            fn go(given self) {
                let result = {
                    let inner_result = {
                        let c = new Container();
                        c.give.get();
                    };
                    inner_result.give;
                };
                let sink = new Sink();
                sink.give.consume(result.give);
                ();
            }
        }
    });
}

// ---------------------------------------------------------------------------
// Block result type doesn't reference locals — passes through unchanged
// ---------------------------------------------------------------------------

/// Block creates a local but returns a freshly constructed value.
/// No normalization needed — should just work.
#[test]
fn block_result_no_local_refs() {
    crate::assert_ok!({
        class Data {}
        class Main {
            fn go(given self) {
                let result = {
                    let unused = new Data();
                    new Data();
                };
                ();
            }
        }
    });
}

// ---------------------------------------------------------------------------
// Copy types through block boundaries
// ---------------------------------------------------------------------------

/// Copy type (Int) returned from block — permission stripping makes
/// this trivially fine regardless of how it was obtained.
#[test]
fn block_copy_type_through_boundary() {
    crate::assert_ok!({
        class Main {
            fn go(given self) {
                let result = {
                    let x = 42;
                    x.give;
                };
                ();
            }
        }
    });
}

use formality_core::test;

// =============================================================================
// Phase 2a: Tests for output renaming + normalization
//
// These tests exercise call-site resolution of return types that reference
// method parameters. They cover:
// - given[self] resolution (currently works by accident via Var::This bug)
// - given[self] where caller has different self permission (exposes bug)
// - Dangling borrows (ref from given — should error)
// - Borrow chaining (ref through ref — should succeed)
// - Multi-place resolution producing Or
//
// All tests should fail until Phase 2b lands.
// =============================================================================

// ---------------------------------------------------------------------------
// given[self] resolution
// ---------------------------------------------------------------------------

/// Basic: method returns given[self] with given self.
/// Currently passes by accident (Var::This collision).
/// After fix, should still pass with correct resolution.
#[test]
fn given_self_basic() {
    crate::assert_ok!({
        class Data {}
        class Container {
            fn get(given self) -> given[self] Data {
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
/// is given. The return type given[self] should resolve to given (from
/// Container's given self), NOT ref (from Caller's ref self).
///
/// After the call, `result` should be `given Data`, so giving it away should work.
#[test]
fn given_self_different_caller_perm() {
    crate::assert_ok!({
        class Data {}
        class Container {
            fn get(given self) -> given[self] Data {
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

/// Named parameter: method returns given[x] where x is a named parameter.
/// The return type should resolve based on x's binding at the call site.
#[test]
fn given_named_param() {
    crate::assert_ok!({
        class Data {}
        class Funcs {
            fn take(given self, x: given Data) -> given[x] Data {
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

/// Named parameter given resolution: result should be given, so
/// giving it to a consumer should work.
#[test]
fn given_named_param_give_result() {
    crate::assert_ok!({
        class Data {}
        class Funcs {
            fn take(given self, x: given Data) -> given[x] Data {
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
    }, expect_test::expect![[r#"
        the rule "keep non-popped link" at (pop_normalize.rs) failed because
          condition evaluated to false: `!link_references_popped(&link, &popped_vars)`
            &link = Rfd(@ fresh(0))
            &popped_vars = [@ fresh(0)]

        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Container, c: Container}, assumptions: {}, fresh: 1 } }

        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Container, c: Container}, assumptions: {}, fresh: 1 } }"#]]);
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
        the rule "keep non-popped link" at (pop_normalize.rs) failed because
          condition evaluated to false: `!link_references_popped(&link, &popped_vars)`
            &link = Rfd(@ fresh(1))
            &popped_vars = [@ fresh(1), @ fresh(0)]

        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Funcs, @ fresh(1): Data, d: Data, f: Funcs}, assumptions: {}, fresh: 2 } }

        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Funcs, @ fresh(1): Data, d: Data, f: Funcs}, assumptions: {}, fresh: 2 } }"#]]);
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
        the rule "keep non-popped link" at (pop_normalize.rs) failed because
          condition evaluated to false: `!link_references_popped(&link, &popped_vars)`
            &link = Rfd(@ fresh(1))
            &popped_vars = [@ fresh(2), @ fresh(1), @ fresh(0)]

        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Funcs, @ fresh(1): Data, @ fresh(2): Data, d1: Data, d2: Data, f: Funcs}, assumptions: {}, fresh: 3 } }

        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Funcs, @ fresh(1): Data, @ fresh(2): Data, d1: Data, d2: Data, f: Funcs}, assumptions: {}, fresh: 3 } }"#]]);
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
    }, expect_test::expect![[r#"
        the rule "keep non-popped link" at (pop_normalize.rs) failed because
          condition evaluated to false: `!link_references_popped(&link, &popped_vars)`
            &link = Rfd(@ fresh(2))
            &popped_vars = [@ fresh(2), @ fresh(1), @ fresh(0)]

        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Funcs, @ fresh(1): ref [d1] Data, @ fresh(2): Data, d1: Data, d2: Data, f: Funcs}, assumptions: {}, fresh: 3 } }

        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Funcs, @ fresh(1): ref [d1] Data, @ fresh(2): Data, d1: Data, d2: Data, f: Funcs}, assumptions: {}, fresh: 3 } }"#]]);
}

// ---------------------------------------------------------------------------
// Perm-dependent dangling: same method, outcome depends on caller's perm
// ---------------------------------------------------------------------------

/// fn foo[perm P](x: P Data) -> ref[x] Data
/// Called with ref arg → borrow chains through, result is valid.
#[test]
fn perm_dependent_borrow_ref_arg_ok() {
    crate::assert_ok!({
        class Data {}
        class Funcs {
            fn foo[perm P](given self, x: P Data) -> ref[x] Data
            where P is copy
            {
                x.ref;
            }
        }
        class Main {
            fn go(given self) {
                let d = new Data();
                let f = new Funcs();
                let result = f.give.foo[ref[d]](d.ref);
                ();
            }
        }
    });
}

/// fn foo[perm P](x: P Data) -> ref[x] Data
/// Called with given arg → dangling borrow. The ref borrows from an
/// owned value that will be dropped when the method's fresh temp is popped.
///
/// Note: no `where P is copy` constraint — that would reject `P = given`
/// at the predicate level before the call site is reached, hiding the
/// dangling borrow error we're testing for.
#[test]
fn perm_dependent_borrow_given_arg_dangles() {
    crate::assert_err!({
        class Data {}
        class Funcs {
            fn foo[perm P](given self, x: P Data) -> ref[x] Data {
                x.ref;
            }
        }
        class Main {
            fn go(given self) {
                let d = new Data();
                let f = new Funcs();
                let result = f.give.foo[given](d.give);
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "keep non-popped link" at (pop_normalize.rs) failed because
          condition evaluated to false: `!link_references_popped(&link, &popped_vars)`
            &link = Rfd(@ fresh(1))
            &popped_vars = [@ fresh(1), @ fresh(0)]

        src/type_system/predicates.rs:623:1: no applicable rules for prove_mut_predicate { p: given, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Funcs, @ fresh(1): Data, d: Data, f: Funcs}, assumptions: {}, fresh: 2 } }

        src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Funcs, @ fresh(1): Data, d: Data, f: Funcs}, assumptions: {}, fresh: 2 } }"#]]);
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

/// given[x, y] with both given args → produces or(given, given) = given.
/// Result should be fully owned.
#[test]
fn multi_place_given_both_given() {
    crate::assert_ok!({
        class Data {}
        class Funcs {
            fn pick(given self, x: given Data, y: given Data) -> given[x, y] Data {
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

// ---------------------------------------------------------------------------
// Borrow-checker interaction via normalization:
// Method calls that produce Or permissions must restrict source places.
// These depend on Phase 2b normalization to produce the correct liens.
// ---------------------------------------------------------------------------

/// Normalized or(ref[d1], ref[d2]) should block giving d1 while result is live.
#[test]
fn norm_or_ref_blocks_give_d1() {
    crate::assert_err!({
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
                d1.give;
                result.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluated to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = @ fresh(0)
            shared_place = @ fresh(0)"#]]);
}

/// Normalized or(mut[d1], mut[d2]) should block mutating d1 while result is live.
#[test]
fn norm_or_mut_blocks_mut_d1() {
    crate::assert_err!({
        class Data {
            fn write(mut[self] self) { (); }
        }
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
                d1.mut.write();
                result.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluated to false: `place_disjoint_from(accessed_place, leased_place)`
            accessed_place = d1
            leased_place = d1"#]]);
}

/// Normalized or(shared mut[d1], shared mut[d2]) from ref-through-mut
/// should block mutating d1 while result is live.
#[test]
fn norm_or_shared_mut_blocks_mut_d1() {
    crate::assert_err!({
        class Data {
            fn write(mut[self] self) { (); }
        }
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
                d1.mut.write();
                result.give;
                ();
            }
        }
    }, expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluated to false: `place_disjoint_from(accessed_place, leased_place)`
            accessed_place = d1
            leased_place = d1"#]]);
}

/// After normalized or-borrowed result is dead, d1 and d2 should be accessible.
#[test]
fn norm_or_ref_allows_give_after_result_dead() {
    crate::assert_ok!({
        class Data {}
        class Funcs {
            fn either[perm P, perm Q](given self, x: P Data, y: Q Data) -> ref[x, y] Data
            where P is copy, Q is copy
            {
                x.ref;
            }
        }
        class Sink {
            fn consume(given self, d: given Data) { (); }
        }
        class Main {
            fn go(given self) {
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

use formality_core::test;

#[test]
#[allow(non_snake_case)]
fn shared_dead_leased_to_our_leased() {
    crate::assert_ok!({
        class Data {
            fn read[perm P](P self) where P is copy {
                ();
            }
        }
        class Main {
            fn test(given self) {
                let d = new Data();
                let p: mut[d] Data = d.mut;
                let q: ref[p] Data = p.ref;
                let r: shared mut[d] Data = q.give;
                r.give.read[shared mut[d]]();
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn shared_live_leased_to_our_leased() {
    // Cannot coerce from `ref[p] mut[d]` to `shared mut[d]`
    // because `p` is not dead.
    crate::assert_err!({
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test(given self) {
                let d = new Data();
                let p: mut[d] Data = d.mut;
                let q: ref[p] Data = p.ref;
                let r: shared mut[d] Data = q.give;
                p.give.read[mut[d]]();
            }
        }
        }, expect_test::expect![[r#"
            the rule "(ref::P) vs (shared::mut::P)" at (redperms.rs) failed because
              condition evaluated to false: `place_b.is_prefix_of(place_a)`
                place_b = d
                place_a = p

            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: mut [d], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }

            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: ref [p] Data}, assumptions: {}, fresh: 0 } }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn leased_dead_leased_to_leased() {
    // Can coerce from `mut[p] mut[d]` to `mut[d]`
    // because `p` is dead.
    crate::assert_ok!({
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test(given self) {
                let d = new Data();
                let p: mut[d] Data = d.mut;
                let q: mut[p] Data = p.mut;
                let r: mut[d] Data = q.give;
                r.give.read[mut[d]]();
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn leased_live_leased_to_leased() {
    // Cannot coerce from `mut[p] mut[d]` to `mut[d]`
    // because `p` is not dead.
    crate::assert_err!({
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test(given self) {
                let d = new Data();
                let p: mut[d] Data = d.mut;
                let q: mut[p] Data = p.mut;
                let r: mut[d] Data = q.give;
                p.give.read[mut[d]]();
            }
        }
        }, expect_test::expect![[r#"
            the rule "(mut::P) vs (mut::P)" at (redperms.rs) failed because
              condition evaluated to false: `place_b.is_prefix_of(place_a)`
                place_b = d
                place_a = p

            src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: mut [p], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, d: Data, p: mut [d] Data, q: mut [p] Data}, assumptions: {}, fresh: 0 } }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn return_leased_dead_leased_to_leased() {
    // Equivalent of `fn test(given self, d: leased Data) -> mut[d] Data
    crate::assert_ok!({
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test[perm P](given self, d: P Data) -> mut[d] Data
            where
                P is mut,
            {
                let p: mut[d] Data = d.mut;
                let q: mut[p] Data = p.mut;
                q.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn return_leased_dead_leased_to_leased_and_use_while_leased() {
    // Equivalent of `fn test(given self, d: leased Data) -> mut[d] Data
    crate::assert_err!({
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test[perm P](given self, d: P Data) -> mut[d] Data
            where
                P is mut,
            {
                let p: mut[d] Data = d.mut;
                let q: mut[p] Data = p.mut;
                p.ref.read[ref[p] Data]();
                q.give;
            }
        }
        }, expect_test::expect![[r#"
            the rule "lease-mutation" at (accesses.rs) failed because
              condition evaluated to false: `place_disjoint_from(accessed_place, leased_place)`
                accessed_place = p
                leased_place = p"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_leased_P_leased_P_data_to_P_data() {
    crate::assert_ok!({
        class Data {
        }
        class Main {
            fn test[perm P](given self, data: P Data) -> P Data
            where
                P is mut,
            {
                let p: mut[data] Data = data.mut;
                p.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn forall_leased_P_shared_P_data_to_our_P_data() {
    crate::assert_ok!({
        class Data {
        }
        class Main {
            fn test[perm P](given self, data: P Data) -> shared P Data
            where
                P is mut,
            {
                let p: ref[data] Data = data.ref;
                p.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn forall_shared_P_ref_P_data_to_our_P_data() {
    crate::assert_ok!({
        class Data {
        }
        class Main {
            fn test[perm P](given self, data: P Data) -> shared P Data
            where
                P is copy,
            {
                let p: ref[data] Data = data.ref;
                p.give;
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn foo_bar_baz() {
    // Can coerce from `mut[p] mut[d]` to `mut[d]`
    // because `p` is dead.
    crate::assert_ok!({
        class Pair[ty A, ty B] {
            a: A;
            b: B;
        }
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test[perm Q, perm R](
              given self, 
              pair: Pair[Q Data, R Data],
              data: mut[pair] Q Data,
            )
            where
                Q is mut,
                R is mut,
            {
                let data2: Q Data = data.give;
            }
        }
        });
}

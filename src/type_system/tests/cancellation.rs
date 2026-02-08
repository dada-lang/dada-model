use formality_core::test;

#[test]
#[allow(non_snake_case)]
fn shared_dead_leased_to_our_leased() {
    crate::assert_ok!("
        class Data {
            fn read[perm P](P self) where shared(P) {
                ();
            }
        }
        class Main {
            fn test(my self) {
                let d = new Data();
                let p: mut[d] Data = d.mut;
                let q: ref[p] Data = p.ref;
                let r: our mut[d] Data = q.move;
                r.move.read[our mut[d]]();
            }
        }
        ");
}

#[test]
#[allow(non_snake_case)]
fn shared_live_leased_to_our_leased() {
    // Cannot coerce from `ref[p] mut[d]` to `our mut[d]`
    // because `p` is not dead.
    crate::assert_err!("
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test(my self) {
                let d = new Data();
                let p: mut[d] Data = d.mut;
                let q: ref[p] Data = p.ref;
                let r: our mut[d] Data = q.move;
                p.move.read[mut[d]]();
            }
        }
        ", expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`

            the rule "(ref::P) vs (our::mut::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                place_b = d
                &place_a = p"#]]);
}

#[test]
#[allow(non_snake_case)]
fn leased_dead_leased_to_leased() {
    // Can coerce from `mut[p] mut[d]` to `mut[d]`
    // because `p` is dead.
    crate::assert_ok!("
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test(my self) {
                let d = new Data();
                let p: mut[d] Data = d.mut;
                let q: mut[p] Data = p.mut;
                let r: mut[d] Data = q.move;
                r.move.read[mut[d]]();
            }
        }
        ");
}

#[test]
#[allow(non_snake_case)]
fn leased_live_leased_to_leased() {
    // Cannot coerce from `mut[p] mut[d]` to `mut[d]`
    // because `p` is not dead.
    crate::assert_err!("
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test(my self) {
                let d = new Data();
                let p: mut[d] Data = d.mut;
                let q: mut[p] Data = p.mut;
                let r: mut[d] Data = q.move;
                p.move.read[mut[d]]();
            }
        }
        ", expect_test::expect![[r#"
            the rule "(mut::P) vs (mut::P)" at (redperms.rs) failed because
              condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                place_b = d
                &place_a = p

            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn return_leased_dead_leased_to_leased() {
    // Equivalent of `fn test(my self, d: leased Data) -> mut[d] Data
    crate::assert_ok!("
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test[perm P](my self, d: P Data) -> mut[d] Data
            where
                leased(P),
            {
                let p: mut[d] Data = d.mut;
                let q: mut[p] Data = p.mut;
                q.move;
            }
        }
        ");
}

#[test]
#[allow(non_snake_case)]
fn return_leased_dead_leased_to_leased_and_use_while_leased() {
    // Equivalent of `fn test(my self, d: leased Data) -> mut[d] Data
    crate::assert_err!("
        class Data {
            fn read[perm P](P self) {
                ();
            }
        }
        class Main {
            fn test[perm P](my self, d: P Data) -> mut[d] Data
            where
                leased(P),
            {
                let p: mut[d] Data = d.mut;
                let q: mut[p] Data = p.mut;
                p.ref.read[ref[p] Data]();
                q.move;
            }
        }
        ", expect_test::expect![[r#"
            the rule "lease-mutation" at (accesses.rs) failed because
              condition evaluted to false: `place_disjoint_from(&accessed_place, &leased_place)`
                &accessed_place = p
                &leased_place = p"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_leased_P_leased_P_data_to_P_data() {
    crate::assert_ok!("
        class Data {
        }
        class Main {
            fn test[perm P](my self, data: P Data) -> P Data
            where
                leased(P),
            {
                let p: mut[data] Data = data.mut;
                p.move;
            }
        }
        ");
}

#[test]
#[allow(non_snake_case)]
fn forall_leased_P_shared_P_data_to_our_P_data() {
    crate::assert_ok!("
        class Data {
        }
        class Main {
            fn test[perm P](my self, data: P Data) -> our P Data
            where
                leased(P),
            {
                let p: ref[data] Data = data.ref;
                p.move;
            }
        }
        ");
}

#[test]
#[allow(non_snake_case)]
fn forall_shared_P_ref_P_data_to_our_P_data() {
    crate::assert_ok!("
        class Data {
        }
        class Main {
            fn test[perm P](my self, data: P Data) -> our P Data
            where
                shared(P),
            {
                let p: ref[data] Data = data.ref;
                p.move;
            }
        }
        ");
}

#[test]
#[allow(non_snake_case)]
fn foo_bar_baz() {
    // Can coerce from `mut[p] mut[d]` to `mut[d]`
    // because `p` is dead.
    crate::assert_ok!("
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
              my self, 
              pair: Pair[Q Data, R Data],
              data: mut[pair] Q Data,
            )
            where
                leased(Q),
                leased(R),
            {
                let data2: Q Data = data.move;
            }
        }
        ");
}

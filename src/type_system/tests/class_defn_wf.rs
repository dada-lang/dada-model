use formality_core::test;

mod our_vs_share;

#[test]
#[allow(non_snake_case)]
fn create_PairSh_with_non_shared_type() {
    crate::assert_err!("
        class Data {}
        class PairSh[ty T]
        where
            shared(T),
        {
        }
        class Main {
            fn test(my self) {
                new PairSh[Data]();
                ();
            }
        }
        ", expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn take_PairSh_with_non_shared_type() {
    crate::assert_err!("
        class Data {}
        class PairSh[ty T]
        where
            shared(T),
        {
        }
        class Main {
            fn test(my self, input: PairSh[Data]) {
                ();
            }
        }
        ", expect_test::expect![[r#"
            the rule "parameter" at (predicates.rs) failed because
              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn take_PairSh_with_shared_type() {
    crate::assert_ok!("
        class Data {}
        class PairSh[ty T]
        where
            shared(T),
        {
        }
        class Main {
            fn test(my self, input: PairSh[our Data]) {
                ();
            }
        }
        ");
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_PT_requires_relative() {
    crate::assert_err!("
        class Ref[perm P, ty T]
        {
            field: P T;
        }
        ", expect_test::expect![[r#"judgment had no applicable rules: `prove_predicate { predicate: relative(!ty_1), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_rel_T_PT_requires_relative() {
    crate::assert_ok!("
        class Ref[perm P, ty T]
        where
            relative(T),
        {
            field: P T;
        }
        ");
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_f1_T_f2_P_shared_f1_ok() {
    // Applying P to shared(self.f1) doesn't imply that
    // typeof(self.f1)=T must be considered relative;
    // the context in which a `shared` appears is not
    // relevant and will be discarded.
    crate::assert_ok!("
        class Data { }
        class Ref[perm P, ty T]
        {
            f1: T;
            f2: P ref[self.f1] Data;
        }
        ");
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_f1_T_f2_P_leased_f1_err() {
    // Applying P to mut[self.f1] requires T to be relative:
    // consider `our Ref[mut[foo], Data]`. If we transformed
    // that to `our Ref[our mut[foo], our Data]`, the type of
    // `f2` would change in important ways.
    crate::assert_err!("
        class Data { }
        class Ref[perm P, ty T]
        {
            f1: T;
            f2: P mut[self.f1] Data;
        }
        ", expect_test::expect![[r#"judgment had no applicable rules: `prove_predicate { predicate: relative(mut [self . f1]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_f1_T_f2_P_moved_f1_err() {
    // Applying P to moved[self.f1] requires T to be relative:
    // consider `our Ref[mut[foo], Data]`. If we transformed
    // that to `our Ref[our mut[foo], our Data]`, the type of
    // `f2` would change in important ways.
    crate::assert_err!("
        class Data { }
        class Ref[perm P, ty T]
        {
            f1: T;
            f2: P moved[self.f1] Data;
        }
        ", expect_test::expect![[r#"judgment had no applicable rules: `prove_predicate { predicate: relative(moved [self . f1]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_rel_T_f1_T_f2_P_moved_f1_ok() {
    crate::assert_ok!("
        class Data { }
        class Ref[perm P, ty T]
        where
            relative(T),
        {
            f1: T;
            f2: P moved[self.f1] Data;
        }
        ");
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_P_Vec_T_err() {
    crate::assert_err!("
        class Data { }
        class Vec[ty T] {
            f1: T;
        }
        class Ref[perm P, ty T]
        {
            f1: P Vec[T];
        }
        ", expect_test::expect![[r#"judgment had no applicable rules: `prove_predicate { predicate: relative(Vec[!ty_1]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn Ref1_requires_rel_Ref2_does_not_err() {
    crate::assert_err!("
        class Ref1[perm P, ty T]
        where
            relative(T),
        {
            f1: P T;
        }
        class Ref2[ty T] {
            f1: Ref1[our, T];
        }
      ", expect_test::expect![[r#"judgment had no applicable rules: `prove_predicate { predicate: relative(!ty_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!ty_0], local_variables: {self: Ref2[!ty_0]}, assumptions: {}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn sh_from_arena() {
    crate::assert_err!("
        class Arena { }
        class Ref[ty T]
        {
            arena: Arena;
            f1: ref[self.arena] T;
        }
      ", expect_test::expect![[r#"judgment had no applicable rules: `prove_predicate { predicate: relative(!ty_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!ty_0], local_variables: {self: Ref[!ty_0]}, assumptions: {}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn atomic_field_req_atomic_err() {
    crate::assert_err!("
        class Atomic[ty T]
        {
            atomic f1: T;
        }
      ", expect_test::expect![[r#"judgment had no applicable rules: `prove_predicate { predicate: atomic(!ty_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!ty_0], local_variables: {self: Atomic[!ty_0]}, assumptions: {}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn atomic_field_req_atomic_ok() {
    crate::assert_ok!("
        class Atomic[ty T]
        where
          atomic(T),
        {
            atomic f1: T;
        }
      ");
}

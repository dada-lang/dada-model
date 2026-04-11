use formality_core::test;

mod shared_vs_share;

#[test]
#[allow(non_snake_case)]
fn create_PairSh_with_non_shared_type() {
    crate::assert_err!({
        class Data {}
        class PairSh[ty T]
        where
            T is copy,
        {
        }
        class Main {
            fn test(given self) {
                new PairSh[Data]();
                ();
            }
        }
        }, expect_test::expect![[r#"src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn take_PairSh_with_non_shared_type() {
    crate::assert_err!({
        class Data {}
        class PairSh[ty T]
        where
            T is copy,
        {
        }
        class Main {
            fn test(given self, input: PairSh[Data]) {
                ();
            }
        }
        }, expect_test::expect![[r#"src/type_system/predicates.rs:324:1: no applicable rules for prove_copy_predicate { p: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, input: PairSh[Data]}, assumptions: {}, fresh: 0 } }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn take_PairSh_with_shared_type() {
    crate::assert_ok!({
        class Data {}
        class PairSh[ty T]
        where
            T is copy,
        {
        }
        class Main {
            fn test(given self, input: PairSh[shared Data]) {
                ();
            }
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_PT_requires_relative() {
    crate::assert_err!({
        class Ref[perm P, ty T]
        {
            field: P T;
        }
        }, expect_test::expect![[r#"src/type_system/predicates.rs:832:1: no applicable rules for variance_predicate { kind: relative, parameter: !ty_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_rel_T_PT_requires_relative() {
    crate::assert_ok!({
        class Ref[perm P, ty T]
        where
            T is relative,
        {
            field: P T;
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_f1_T_f2_P_shared_f1_ok() {
    // Applying P to shared(self.f1) doesn't imply that
    // typeof(self.f1)=T must be considered relative;
    // the context in which a `shared` appears is not
    // relevant and will be discarded.
    crate::assert_ok!({
        class Data { }
        class Ref[perm P, ty T]
        {
            f1: T;
            f2: P ref[self.f1] Data;
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_f1_T_f2_P_leased_f1_err() {
    // Applying P to mut[self.f1] requires T to be relative:
    // consider `shared Ref[mut[foo], Data]`. If we transformed
    // that to `shared Ref[shared mut[foo], shared Data]`, the type of
    // `f2` would change in important ways.
    crate::assert_err!({
        class Data { }
        class Ref[perm P, ty T]
        {
            f1: T;
            f2: P mut[self.f1] Data;
        }
        }, expect_test::expect![[r#"src/type_system/predicates.rs:832:1: no applicable rules for variance_predicate { kind: relative, parameter: !ty_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_f1_T_f2_P_given_f1_err() {
    // Applying P to given[self.f1] requires T to be relative:
    // consider `shared Ref[mut[foo], Data]`. If we transformed
    // that to `shared Ref[shared mut[foo], shared Data]`, the type of
    // `f2` would change in important ways.
    crate::assert_err!({
        class Data { }
        class Ref[perm P, ty T]
        {
            f1: T;
            f2: P given[self.f1] Data;
        }
        }, expect_test::expect![[r#"src/type_system/predicates.rs:832:1: no applicable rules for variance_predicate { kind: relative, parameter: !ty_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_rel_T_f1_T_f2_P_given_f1_ok() {
    crate::assert_ok!({
        class Data { }
        class Ref[perm P, ty T]
        where
            T is relative,
        {
            f1: T;
            f2: P given[self.f1] Data;
        }
        });
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_P_Vec_T_err() {
    crate::assert_err!({
        class Data { }
        class Vec[ty T] {
            f1: T;
        }
        class Ref[perm P, ty T]
        {
            f1: P Vec[T];
        }
        }, expect_test::expect![[r#"src/type_system/predicates.rs:832:1: no applicable rules for variance_predicate { kind: relative, parameter: !ty_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn Ref1_requires_rel_Ref2_does_not_err() {
    crate::assert_err!({
        class Ref1[perm P, ty T]
        where
            T is relative,
        {
            f1: P T;
        }
        class Ref2[ty T] {
            f1: Ref1[shared, T];
        }
      }, expect_test::expect![[r#"src/type_system/predicates.rs:832:1: no applicable rules for variance_predicate { kind: relative, parameter: !ty_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!ty_0], local_variables: {self: Ref2[!ty_0]}, assumptions: {}, fresh: 0 } }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn sh_from_arena() {
    crate::assert_err!({
        class Arena { }
        class Ref[ty T]
        {
            arena: Arena;
            f1: ref[self.arena] T;
        }
      }, expect_test::expect![[r#"src/type_system/predicates.rs:832:1: no applicable rules for variance_predicate { kind: relative, parameter: !ty_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!ty_0], local_variables: {self: Ref[!ty_0]}, assumptions: {}, fresh: 0 } }"#]]);
}

#[test]
#[allow(non_snake_case)]
fn atomic_field_req_atomic_err() {
    crate::assert_err!({
        class Atomic[ty T]
        {
            atomic f1: T;
        }
      }, expect_test::expect![[r#"
          the rule "check_field" at (classes.rs) failed because
            judgment `prove_predicate { predicate: !ty_0 is atomic, env: Env { program: "...", universe: universe(1), in_scope_vars: [!ty_0], local_variables: {self: Atomic[!ty_0]}, assumptions: {!ty_0 is share}, fresh: 0 } }` failed at the following rule(s):
              the rule "variance" at (predicates.rs) failed because
                src/type_system/predicates.rs:832:1: judgment had no applicable rules: `variance_predicate { kind: atomic, parameter: !ty_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!ty_0], local_variables: {self: Atomic[!ty_0]}, assumptions: {!ty_0 is share}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn atomic_field_req_atomic_ok() {
    crate::assert_ok!({
        class Atomic[ty T]
        where
          T is atomic,
        {
            atomic f1: T;
        }
      });
}

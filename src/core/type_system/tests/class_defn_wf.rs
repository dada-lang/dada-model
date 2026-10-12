use formality_core::test;

mod shared_vs_share;

#[test]
#[allow(non_snake_case)]
fn create_PairSh_with_non_shared_type() {
    crate::assert_err!(r#"
        struct Data {}
        struct PairSh[type T]
        where
            T is shared,
        {
        }
        struct Main {
            fn test(given self) {
                new PairSh[Data]();
                ();
            }
        }
        "#, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct PairSh [type] where ^type0_0 is shared { } struct Main { fn test (given self) → () { new PairSh [Data] () ; () ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn take_PairSh_with_non_shared_type() {
    crate::assert_err!(
        r#"
        struct Data {}
        struct PairSh[type T]
        where
            T is shared,
        {
        }
        struct Main {
            fn test(given self, input: given PairSh[Data]) {
                ();
            }
        }
        "#,
        expect_test::expect![[r#"
            the rule "apply_perm" at (types.rs) failed because
              condition evaluted to false: `*perm != Perm::Given`"#]]
    );
}

#[test]
#[allow(non_snake_case)]
fn take_PairSh_with_shared_type() {
    crate::assert_ok!(
        r#"
    struct Data {}
    struct PairSh[type T]
    where
        T is shared,
    {
    }
    struct Main {
        fn test(given self, input: given PairSh[shared Data]) {
            ();
        }
    }
    "#
    );
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_PT_requires_relative() {
    crate::assert_err!(r#"
        struct Ref[perm P, type T]
        {
            field: P T;
        }
        "#, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Ref [perm, type] { field : ^perm0_0 ^type0_1 ; } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_rel_T_PT_requires_relative() {
    crate::assert_ok!(
        r#"
    struct Ref[perm P, type T]
    where
        T is relative,
    {
        field: P T;
    }
    "#
    );
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_f1_T_f2_P_shared_f1_ok() {
    // Applying P to shared(self.f1) doesn't imply that
    // typeof(self.f1)=T must be considered relative;
    // the context in which a `shared` appears is not
    // relevant and will be discarded.
    crate::assert_ok!(
        r#"
    struct Data { }
    struct Ref[perm P, type T]
    {
        f1: T;
        f2: P shared[self.f1] Data;
    }
    "#
    );
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_f1_T_f2_P_leased_f1_err() {
    // Applying P to ![self.f1] requires T to be relative:
    // consider `shared Ref[![foo], Data]`. If we transformed
    // that to `shared Ref[shared ![foo], shared Data]`, the type of
    // `f2` would change in important ways.
    crate::assert_err!(r#"
        struct Data { }
        struct Ref[perm P, type T]
        {
            f1: T;
            f2: P ![self.f1] Data;
        }
        "#, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Ref [perm, type] { f1 : ^type0_1 ; f2 : ^perm0_0 ! [self . f1] Data ; } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_f1_T_f2_P_given_from_f1_err() {
    // Applying P to given[self.f1] requires T to be relative:
    // consider `shared Ref[![foo], Data]`. If we transformed
    // that to `shared Ref[shared ![foo], shared Data]`, the type of
    // `f2` would change in important ways.
    crate::assert_err!(r#"
        struct Data { }
        struct Ref[perm P, type T]
        {
            f1: T;
            f2: P given[self.f1] Data;
        }
        "#, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Ref [perm, type] { f1 : ^type0_1 ; f2 : ^perm0_0 given [self . f1] Data ; } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_rel_T_f1_T_f2_P_given_from_f1_ok() {
    crate::assert_ok!(
        r#"
    struct Data { }
    struct Ref[perm P, type T]
    where
        T is relative,
    {
        f1: T;
        f2: P given[self.f1] Data;
    }
    "#
    );
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_P_Vec_T_err() {
    crate::assert_err!(r#"
        struct Data { }
        struct Vec[type T] {
            f1: T;
        }
        struct Ref[perm P, type T]
        {
            f1: P Vec[T];
        }
        "#, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Vec [type] { f1 : ^type0_0 ; } struct Ref [perm, type] { f1 : ^perm0_0 Vec[^type0_1] ; } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn Ref1_requires_rel_Ref2_does_not_err() {
    crate::assert_err!(r#"
        struct Ref1[perm P, type T]
        where
            T is relative,
        {
            f1: P T;
        }
        struct Ref2[type T] {
            f1: Ref1[shared, T];
        }
      "#, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Ref1 [perm, type] where ^type0_1 is relative { f1 : ^perm0_0 ^type0_1 ; } struct Ref2 [type] { f1 : Ref1[shared, ^type0_0] ; } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn sh_from_arena() {
    crate::assert_err!(r#"
        struct Arena { }
        struct Ref[type T]
        {
            arena: Arena;
            f1: shared[self.arena] T;
        }
      "#, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Arena { } struct Ref [type] { arena : Arena ; f1 : shared [self . arena] ^type0_0 ; } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn atomic_field_req_atomic_err() {
    crate::assert_err!(
        r#"
        struct Atomic[type T]
        {
            atomic f1: T;
        }
      "#,
        expect_test::expect![[r#"
          the rule "check_field" at (classes.rs) failed because
            judgment `prove_predicate { predicate: !type_0 is atomic, env: Env { program: "...", universe: universe(1), in_scope_vars: [!type_0], local_variables: {self: Atomic[!type_0]}, assumptions: {!type_0 is struct}, fresh: 0 } }` failed at the following rule(s):
              the rule "variance" at (predicates.rs) failed because
                judgment had no applicable rules: `variance_predicate { kind: atomic, parameter: !type_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!type_0], local_variables: {self: Atomic[!type_0]}, assumptions: {!type_0 is struct}, fresh: 0 } }`"#]]
    );
}

#[test]
#[allow(non_snake_case)]
fn atomic_field_req_atomic_ok() {
    crate::assert_ok!(
        r#"
      struct Atomic[type T]
      where
        T is atomic,
      {
          atomic f1: T;
      }
    "#
    );
}

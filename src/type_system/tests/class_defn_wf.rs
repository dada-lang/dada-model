use formality_core::test;

mod shared_vs_share;

#[test]
#[allow(non_snake_case)]
fn create_PairSh_with_non_shared_type() {
    crate::assert_err!({
        class Data {}
        class PairSh[ty T]
        where
            copy(T),
        {
        }
        class Main {
            fn test(given self) {
                new PairSh[Data]();
                ();
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self) -> () { new PairSh [Data] () ; () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { new PairSh [Data] () ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { new PairSh [Data] () ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { new PairSh [Data] () ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { new PairSh [Data] () ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { new PairSh [Data] () ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements { statements: [new PairSh [Data] () ;, () ;], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "type_statements" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [new PairSh [Data] () ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statement { statement: new PairSh [Data] () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "expr" at (statements.rs) failed because
                                                  judgment `type_expr { expr: new PairSh [Data] (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "new" at (expressions.rs) failed because
                                                      judgment `prove_predicates { predicate: [copy(Data)], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                        the rule "prove_predicates" at (predicates.rs) failed because
                                                          judgment `prove_predicate { predicate: copy(Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                            the rule "parameter" at (predicates.rs) failed because
                                                              pattern `true` did not match value `false`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn take_PairSh_with_non_shared_type() {
    crate::assert_err!({
        class Data {}
        class PairSh[ty T]
        where
            copy(T),
        {
        }
        class Main {
            fn test(given self, input: PairSh[Data]) {
                ();
            }
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn test (given self input : PairSh[Data]) -> () { () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  check type `PairSh[Data]`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn take_PairSh_with_shared_type() {
    crate::assert_ok!({
        class Data {}
        class PairSh[ty T]
        where
            copy(T),
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
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_field { decl: field : !perm_0 !ty_1 ;, class_ty: Ref[!perm_0, !ty_1], class_predicate: share, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_field" at (classes.rs) failed because
                  check type `!perm_0 !ty_1`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_rel_T_PT_requires_relative() {
    crate::assert_ok!({
        class Ref[perm P, ty T]
        where
            relative(T),
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
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_field { decl: f2 : !perm_0 mut [self . f1] Data ;, class_ty: Ref[!perm_0, !ty_1], class_predicate: share, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_field" at (classes.rs) failed because
                  check type `!perm_0 mut [self . f1] Data`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_f1_T_f2_P_given_from_f1_err() {
    // Applying P to given_from[self.f1] requires T to be relative:
    // consider `shared Ref[mut[foo], Data]`. If we transformed
    // that to `shared Ref[shared mut[foo], shared Data]`, the type of
    // `f2` would change in important ways.
    crate::assert_err!({
        class Data { }
        class Ref[perm P, ty T]
        {
            f1: T;
            f2: P given_from[self.f1] Data;
        }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_field { decl: f2 : !perm_0 given_from [self . f1] Data ;, class_ty: Ref[!perm_0, !ty_1], class_predicate: share, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_field" at (classes.rs) failed because
                  check type `!perm_0 given_from [self . f1] Data`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_rel_T_f1_T_f2_P_given_from_f1_ok() {
    crate::assert_ok!({
        class Data { }
        class Ref[perm P, ty T]
        where
            relative(T),
        {
            f1: T;
            f2: P given_from[self.f1] Data;
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
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_field { decl: f1 : !perm_0 Vec[!ty_1] ;, class_ty: Ref[!perm_0, !ty_1], class_predicate: share, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_field" at (classes.rs) failed because
                  check type `!perm_0 Vec[!ty_1]`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn Ref1_requires_rel_Ref2_does_not_err() {
    crate::assert_err!({
        class Ref1[perm P, ty T]
        where
            relative(T),
        {
            f1: P T;
        }
        class Ref2[ty T] {
            f1: Ref1[shared, T];
        }
      }, expect_test::expect![[r#"
          the rule "check_class" at (classes.rs) failed because
            judgment `check_field { decl: f1 : Ref1[shared, !ty_0] ;, class_ty: Ref2[!ty_0], class_predicate: share, env: Env { program: "...", universe: universe(1), in_scope_vars: [!ty_0], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
              the rule "check_field" at (classes.rs) failed because
                check type `Ref1[shared, !ty_0]`"#]]);
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
      }, expect_test::expect![[r#"
          the rule "check_class" at (classes.rs) failed because
            judgment `check_field { decl: f1 : ref [self . arena] !ty_0 ;, class_ty: Ref[!ty_0], class_predicate: share, env: Env { program: "...", universe: universe(1), in_scope_vars: [!ty_0], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
              the rule "check_field" at (classes.rs) failed because
                check type `ref [self . arena] !ty_0`"#]]);
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
          the rule "check_class" at (classes.rs) failed because
            judgment `check_field { decl: atomic f1 : !ty_0 ;, class_ty: Atomic[!ty_0], class_predicate: share, env: Env { program: "...", universe: universe(1), in_scope_vars: [!ty_0], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
              the rule "check_field" at (classes.rs) failed because
                judgment `prove_predicate { predicate: atomic(!ty_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!ty_0], local_variables: {self: Atomic[!ty_0]}, assumptions: {share(!ty_0)}, fresh: 0 } }` failed at the following rule(s):
                  the rule "variance" at (predicates.rs) failed because
                    judgment had no applicable rules: `variance_predicate { kind: atomic, parameter: !ty_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!ty_0], local_variables: {self: Atomic[!ty_0]}, assumptions: {share(!ty_0)}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn atomic_field_req_atomic_ok() {
    crate::assert_ok!({
        class Atomic[ty T]
        where
          atomic(T),
        {
            atomic f1: T;
        }
      });
}

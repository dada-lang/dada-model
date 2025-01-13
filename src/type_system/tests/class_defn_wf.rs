use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

#[test]
#[allow(non_snake_case)]
fn create_PairSh_with_non_shared_type() {
    check_program(&term(
        "
        class Data {}
        class PairSh[ty T]
        where
            copy(T),
        {
        }
        class Main {
            fn test(my self) {
                new PairSh[Data]();
                ();
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class PairSh [ty] where copy(^ty0_0) { } class Main { fn test (my self) -> () { new PairSh [Data] () ; () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check function body
            3: judgment `can_type_expr_as { expr: { new PairSh [Data] () ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                 the rule "can_type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `type_expr_as { expr: { new PairSh [Data] () ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                     the rule "type_expr_as" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `type_expr { expr: { new PairSh [Data] () ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                         the rule "block" failed at step #0 (src/file.rs:LL:CC) because
                           judgment `type_block { block: { new PairSh [Data] () ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                             the rule "place" failed at step #0 (src/file.rs:LL:CC) because
                               judgment `type_statements_with_final_ty { statements: [new PairSh [Data] () ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                 the rule "cons" failed at step #1 (src/file.rs:LL:CC) because
                                   judgment `type_statement { statement: new PairSh [Data] () ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                     the rule "expr" failed at step #0 (src/file.rs:LL:CC) because
                                       judgment `type_expr { expr: new PairSh [Data] (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                         the rule "new" failed at step #4 (src/file.rs:LL:CC) because
                                           judgment `prove_predicates { predicate: [copy(Data)], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                             the rule "prove_predicates" failed at step #0 (src/file.rs:LL:CC) because
                                               judgment `prove_predicate { predicate: copy(Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                 the rule "shared" failed at step #0 (src/file.rs:LL:CC) because
                                                   judgment `is_copy { a: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                                                     the rule "is_copy" failed at step #1 (src/file.rs:LL:CC) because
                                                       judgment had no applicable rules: `lien_chain_is_copy { chain: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main}, assumptions: {}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn take_PairSh_with_non_shared_type() {
    check_program(&term(
        "
        class Data {}
        class PairSh[ty T]
        where
            copy(T),
        {
        }
        class Main {
            fn test(my self, input: PairSh[Data]) {
                ();
            }
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class PairSh [ty] where copy(^ty0_0) { } class Main { fn test (my self input : PairSh[Data]) -> () { () ; } }`

        Caused by:
            0: check class named `Main`
            1: check method named `test`
            2: check type `PairSh[Data]`
            3: judgment `prove_predicate { predicate: copy(Data), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, input: PairSh[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                 the rule "shared" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `is_copy { a: Data, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, input: PairSh[Data]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                     the rule "is_copy" failed at step #1 (src/file.rs:LL:CC) because
                       judgment had no applicable rules: `lien_chain_is_copy { chain: my, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: my Main, input: PairSh[Data]}, assumptions: {}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn take_PairSh_with_shared_type() {
    check_program(&term(
        "
        class Data {}
        class PairSh[ty T]
        where
            copy(T),
        {
        }
        class Main {
            fn test(my self, input: PairSh[our Data]) {
                ();
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_PT_requires_relative() {
    check_program(&term(
        "
        class Ref[perm P, ty T]
        {
            field: P T;
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Ref [perm, ty] { field : ^perm0_0 ^ty0_1 ; }`

        Caused by:
            0: check class named `Ref`
            1: check field named `field`
            2: check type `!perm_0 !ty_1`
            3: judgment `prove_predicate { predicate: relative(!ty_1), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                 the rule "variance" failed at step #0 (src/file.rs:LL:CC) because
                   judgment had no applicable rules: `variance_predicate { kind: relative, parameter: !ty_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_rel_T_PT_requires_relative() {
    check_program(&term(
        "
        class Ref[perm P, ty T]
        where
            relative(T),
        {
            field: P T;
        }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_f1_T_f2_P_shared_f1_ok() {
    // Applying P to shared(self.f1) doesn't imply that
    // typeof(self.f1)=T must be considered relative;
    // the context in which a `shared` appears is not
    // relevant and will be discarded.
    check_program(&term(
        "
        class Data { }
        class Ref[perm P, ty T]
        {
            f1: T;
            f2: P shared{self.f1} Data;
        }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_f1_T_f2_P_leased_f1_err() {
    // Applying P to leased{self.f1} requires T to be relative:
    // consider `our Ref[leased{foo}, Data]`. If we transformed
    // that to `our Ref[our leased{foo}, our Data]`, the type of
    // `f2` would change in important ways.
    check_program(&term(
        "
        class Data { }
        class Ref[perm P, ty T]
        {
            f1: T;
            f2: P leased{self.f1} Data;
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Ref [perm, ty] { f1 : ^ty0_1 ; f2 : ^perm0_0 leased {self . f1} Data ; }`

        Caused by:
            0: check class named `Ref`
            1: check field named `f2`
            2: check type `!perm_0 leased {self . f1} Data`
            3: check_perm(!perm_0 leased {self . f1}
            4: judgment `prove_predicate { predicate: relative(leased {self . f1}), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                 the rule "variance" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `variance_predicate { kind: relative, parameter: leased {self . f1}, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                     the rule "leased" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `variance_predicate_place { kind: relative, place: self . f1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "perm" failed at step #1 (src/file.rs:LL:CC) because
                           judgment `prove_predicate { predicate: relative(!ty_1), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "variance" failed at step #0 (src/file.rs:LL:CC) because
                               judgment had no applicable rules: `variance_predicate { kind: relative, parameter: !ty_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_f1_T_f2_P_given_f1_err() {
    // Applying P to given{self.f1} requires T to be relative:
    // consider `our Ref[leased{foo}, Data]`. If we transformed
    // that to `our Ref[our leased{foo}, our Data]`, the type of
    // `f2` would change in important ways.
    check_program(&term(
        "
        class Data { }
        class Ref[perm P, ty T]
        {
            f1: T;
            f2: P given{self.f1} Data;
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Ref [perm, ty] { f1 : ^ty0_1 ; f2 : ^perm0_0 given {self . f1} Data ; }`

        Caused by:
            0: check class named `Ref`
            1: check field named `f2`
            2: check type `!perm_0 given {self . f1} Data`
            3: check_perm(!perm_0 given {self . f1}
            4: judgment `prove_predicate { predicate: relative(given {self . f1}), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                 the rule "variance" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `variance_predicate { kind: relative, parameter: given {self . f1}, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                     the rule "given" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `variance_predicate_place { kind: relative, place: self . f1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "perm" failed at step #1 (src/file.rs:LL:CC) because
                           judgment `prove_predicate { predicate: relative(!ty_1), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                             the rule "variance" failed at step #0 (src/file.rs:LL:CC) because
                               judgment had no applicable rules: `variance_predicate { kind: relative, parameter: !ty_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_rel_T_f1_T_f2_P_given_f1_ok() {
    check_program(&term(
        "
        class Data { }
        class Ref[perm P, ty T]
        where
            relative(T),
        {
            f1: T;
            f2: P given{self.f1} Data;
        }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]]);
}

#[test]
#[allow(non_snake_case)]
fn forall_P_T_P_Vec_T_err() {
    check_program(&term(
        "
        class Data { }
        class Vec[ty T] {
            f1: T;
        }
        class Ref[perm P, ty T]
        {
            f1: P Vec[T];
        }
        ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Data { } class Vec [ty] { f1 : ^ty0_0 ; } class Ref [perm, ty] { f1 : ^perm0_0 Vec[^ty0_1] ; }`

        Caused by:
            0: check class named `Ref`
            1: check field named `f1`
            2: check type `!perm_0 Vec[!ty_1]`
            3: judgment `prove_predicate { predicate: relative(Vec[!ty_1]), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                 the rule "variance" failed at step #0 (src/file.rs:LL:CC) because
                   judgment `variance_predicate { kind: relative, parameter: Vec[!ty_1], env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                     the rule "ty-named" failed at step #0 (src/file.rs:LL:CC) because
                       judgment `prove_predicate { predicate: relative(!ty_1), env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                         the rule "variance" failed at step #0 (src/file.rs:LL:CC) because
                           judgment had no applicable rules: `variance_predicate { kind: relative, parameter: !ty_1, env: Env { program: "...", universe: universe(2), in_scope_vars: [!perm_0, !ty_1], local_variables: {self: Ref[!perm_0, !ty_1]}, assumptions: {}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn Ref1_requires_rel_Ref2_does_not_err() {
    check_program(&term(
        "
        class Ref1[perm P, ty T]
        where
            relative(T),
        {
            f1: P T;
        }
        class Ref2[ty T] {
            f1: Ref1[our, T];
        }
      ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Ref1 [perm, ty] where relative(^ty0_1) { f1 : ^perm0_0 ^ty0_1 ; } class Ref2 [ty] { f1 : Ref1[our, ^ty0_0] ; }`

        Caused by:
            0: check class named `Ref2`
            1: check field named `f1`
            2: check type `Ref1[our, !ty_0]`
            3: judgment `prove_predicate { predicate: relative(!ty_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!ty_0], local_variables: {self: Ref2[!ty_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                 the rule "variance" failed at step #0 (src/file.rs:LL:CC) because
                   judgment had no applicable rules: `variance_predicate { kind: relative, parameter: !ty_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!ty_0], local_variables: {self: Ref2[!ty_0]}, assumptions: {}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn sh_from_arena() {
    check_program(&term(
        "
        class Arena { }
        class Ref[ty T]
        {
            arena: Arena;
            f1: shared{self.arena} T;
        }
      ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Arena { } class Ref [ty] { arena : Arena ; f1 : shared {self . arena} ^ty0_0 ; }`

        Caused by:
            0: check class named `Ref`
            1: check field named `f1`
            2: check type `shared {self . arena} !ty_0`
            3: judgment `prove_predicate { predicate: relative(!ty_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!ty_0], local_variables: {self: Ref[!ty_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                 the rule "variance" failed at step #0 (src/file.rs:LL:CC) because
                   judgment had no applicable rules: `variance_predicate { kind: relative, parameter: !ty_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!ty_0], local_variables: {self: Ref[!ty_0]}, assumptions: {}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn atomic_field_req_atomic_err() {
    check_program(&term(
        "
        class Atomic[ty T]
        {
            atomic f1: T;
        }
      ",
    ))
    .assert_err(expect_test::expect![[r#"
        check program `class Atomic [ty] { atomic f1 : ^ty0_0 ; }`

        Caused by:
            0: check class named `Atomic`
            1: check field named `f1`
            2: judgment `prove_predicate { predicate: atomic(!ty_0), env: Env { program: "...", universe: universe(1), in_scope_vars: [!ty_0], local_variables: {self: Atomic[!ty_0]}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                 the rule "variance" failed at step #0 (src/file.rs:LL:CC) because
                   judgment had no applicable rules: `variance_predicate { kind: atomic, parameter: !ty_0, env: Env { program: "...", universe: universe(1), in_scope_vars: [!ty_0], local_variables: {self: Atomic[!ty_0]}, assumptions: {}, fresh: 0 } }`"#]]);
}

#[test]
#[allow(non_snake_case)]
fn atomic_field_req_atomic_ok() {
    check_program(&term(
        "
        class Atomic[ty T]
        where
          atomic(T),
        {
            atomic f1: T;
        }
      ",
    ))
    .assert_ok(expect_test::expect![["()"]]);
}

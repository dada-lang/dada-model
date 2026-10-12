//! Phase 3a: runtime return normalization and method-scope isolation.
//! Direct frame tests observe permissions and leaked bindings that display/heap
//! snapshots cannot expose. Runtime results retain the branch actually returned.
use crate::{
    dada_lang::term,
    grammar::{Block, Program, Ty},
    interpreter::{Interpreter, StackFrame},
};

const PROGRAM: &str = r#"
    struct Data {
        n: Int;
        fn borrow_self[perm P](P self) -> shared[self] Data { self.share; }
    }
    struct Funcs {
        fn take(given self, x: given Data) -> given[x] Data { x^; }
        fn borrow[perm P](given self, x: P Data) -> shared[x] Data { x.share; }
        fn lease[perm P](given self, x: P Data) -> ![x] Data
        where P is mut { x!; }
        fn either[perm P, perm Q](given self, x: P Data, y: Q Data) -> shared[x, y] Data
        where P is shared, Q is shared { x.share; }
        fn either_mut[perm P, perm Q](given self, x: P Data, y: Q Data) -> ![x, y] Data
        where P is mut, Q is mut { x!; }
        fn pick(given self, x: given Data, y: given Data) -> given[x, y] Data { x^; }
        fn scalar(given self) -> Int { 7; }
    }
"#;

/// Each call starts with owned sources in a caller frame. Inspect the result
/// before dropping caller locals, so borrowing them is valid.
fn check_call(expression: &str, expected_ty: &str, expected_value: &str) {
    let program: Program = term(PROGRAM);
    let _ = crate::type_system::check_program(&program)
        .into_singleton()
        .unwrap();
    let mut interp = Interpreter::new(&program);
    let mut caller = StackFrame {
        env: interp.base_env(),
        variables: vec![],
    };
    let setup: Block =
        term("{ let d1 = new Data(42); let d2 = new Data(99); let f = new Funcs(); }");
    for statement in &setup.statements {
        interp.eval_statement(&mut caller, statement).unwrap();
    }
    let env_before = caller.env.clone();
    let variables_before = caller.variables.clone();
    let result = interp
        .eval_expr_value(&mut caller, &term(expression))
        .unwrap();
    assert_eq!(
        result.ty,
        term::<Ty>(expected_ty),
        "return permission must reference caller-scoped places"
    );
    assert_eq!(
        interp.display_value(&caller.env, &result).unwrap(),
        expected_value
    );
    assert_eq!(
        caller.env, env_before,
        "method-local type bindings must not leak into the caller"
    );
    assert_eq!(caller.variables, variables_before);
}

#[test]
fn scalar_return_does_not_leak_method_bindings() {
    check_call("f^.scalar()", "Int", "7");
}

#[test]
fn given_from_named_parameter() {
    check_call("f^.take(d1^)", "Data", "Data { n: 42 }");
}

#[test]
fn given_from_multiple_parameters() {
    check_call("f^.pick(d1^, d2^)", "Data", "Data { n: 42 }");
}

#[test]
fn ref_through_ref() {
    check_call(
        "f^.borrow[shared[d1]](d1.share)",
        "shared[d1] Data",
        "shared [d1] Data { n: 42 }",
    );
}

#[test]
fn ref_through_receiver() {
    check_call(
        "d1.share.borrow_self[shared[d1]]()",
        "shared[d1] Data",
        "shared [d1] Data { n: 42 }",
    );
}

#[test]
fn mut_through_mut() {
    check_call(
        "f^.lease[![d1]](d1!)",
        "![d1] Data",
        "! [d1] Data { n: 42 }",
    );
}

#[test]
fn ref_through_mut() {
    check_call(
        "f^.borrow[![d1]](d1!)",
        "shared ![d1] Data",
        "shared ! [d1] Data { n: 42 }",
    );
}

#[test]
fn multi_place_ref_keeps_runtime_branch() {
    check_call(
        "f^.either[shared[d1], shared[d2]](d1.share, d2.share)",
        "shared[d1] Data",
        "shared [d1] Data { n: 42 }",
    );
}

#[test]
fn multi_place_mut_keeps_runtime_branch() {
    check_call(
        "f^.either_mut[![d1], ![d2]](d1!, d2!)",
        "![d1] Data",
        "! [d1] Data { n: 42 }",
    );
}

/// Bypass type checking deliberately: Phase 2 rejects this call statically.
/// The interpreter must reject the escaping borrow at the return boundary too,
/// rather than allowing the caller to discover a dropped referent later.
#[test]
fn borrow_of_given_parameter_fails_at_return() {
    let program: Program = term(PROGRAM);
    let mut interp = Interpreter::new(&program);
    let mut caller = StackFrame {
        env: interp.base_env(),
        variables: vec![],
    };
    let result = interp.eval_expr_value(
        &mut caller,
        &term("new Funcs().borrow[given](new Data(42))"),
    );
    let error = result.expect_err("borrow from a consumed parameter must not escape");
    assert!(
        format!("{error:?}").contains("dangling borrow"),
        "{error:?}"
    );
}

#[test]
fn borrow_of_given_receiver_fails_at_return() {
    let program: Program = term(PROGRAM);
    let mut interp = Interpreter::new(&program);
    let mut caller = StackFrame {
        env: interp.base_env(),
        variables: vec![],
    };
    let result = interp.eval_expr_value(&mut caller, &term("new Data(42).borrow_self[given]()"));
    let error = result.expect_err("borrow from a consumed receiver must not escape");
    assert!(
        format!("{error:?}").contains("dangling borrow"),
        "{error:?}"
    );
}

#[test]
fn owned_field_return_through_borrowed_caller() {
    crate::assert_interpret!({
        struct Data { n: Int; }
        struct Container {
            data: Data;
            fn take(given self) -> given[self] Data { self.data^; }
        }
        struct Caller {
            fn run[perm P](P self, c: given Container) -> Data where P is shared {
                c^.take();
            }
        }
        struct Main {
            fn main(given self) -> Data {
                let caller = new Caller();
                caller.share.run[shared[caller]](new Container(new Data(42)));
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_caller = new Caller () ;
        Output: Trace:   _1_caller = Caller {  }
        Output: Trace:   _1_caller . share . run [shared [_1_caller]] (new Container (new Data (42))) ;
        Output: Trace:   enter Caller.run
        Output: Trace:     _2_c ^ . take () ;
        Output: Trace:     enter Container.take
        Output: Trace:       _3_self . data ^ ;
        Output: Trace:     exit Container.take => Data { n: 42 }
        Output: Trace:   exit Caller.run => Data { n: 42 }
        Output: Trace: exit Main.main => Data { n: 42 }
        Result: Ok: Data { n: 42 }
        Alloc 0x0b: [Int(42)]"#]]);
}

#[test]
fn nested_borrow_calls_preserve_value() {
    crate::assert_interpret!({
        struct Data { n: Int; }
        struct Funcs {
            fn borrow[perm P](given self, x: P Data) -> shared[x] Data { x.share; }
        }
        struct Main {
            fn main(given self) -> Int {
                let d = new Data(42);
                let f = new Funcs();
                let r = f^.borrow[shared[d]](d.share);
                let g = new Funcs();
                let s = g^.borrow[shared[d]](r^);
                s.n^ + 1;
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d = new Data (42) ;
        Output: Trace:   _1_d = Data { n: 42 }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_r = _1_f ^ . borrow [shared [_1_d]] (_1_d . share) ;
        Output: Trace:   enter Funcs.borrow
        Output: Trace:     _2_x . share ;
        Output: Trace:   exit Funcs.borrow => shared [_1_d] Data { n: 42 }
        Output: Trace:   _1_r = shared [_1_d] Data { n: 42 }
        Output: Trace:   let _1_g = new Funcs () ;
        Output: Trace:   _1_g = Funcs {  }
        Output: Trace:   let _1_s = _1_g ^ . borrow [shared [_1_d]] (_1_r ^) ;
        Output: Trace:   enter Funcs.borrow
        Output: Trace:     _3_x . share ;
        Output: Trace:   exit Funcs.borrow => shared [_1_d] Data { n: 42 }
        Output: Trace:   _1_s = shared [_1_d] Data { n: 42 }
        Output: Trace:   _1_s . n ^ + 1 ;
        Output: Trace: exit Main.main => 43
        Result: Ok: 43
        Alloc 0x15: [Int(43)]"#]]);
}

//! Phase 3a: runtime return normalization and method-scope isolation.
//! Direct frame tests observe permissions and leaked bindings that display/heap
//! snapshots cannot expose. Runtime results retain the branch actually returned.
use crate::{
    dada_lang::term,
    grammar::{Block, Program, Ty},
    interpreter::{Interpreter, StackFrame},
};

const PROGRAM: &str = r#"
    class Data {
        n: Int;
        fn borrow_self[perm P](P self) -> ref[self] Data { self.ref; }
    }
    class Funcs {
        fn take(given self, x: given Data) -> given_from[x] Data { x.give; }
        fn borrow[perm P](given self, x: P Data) -> ref[x] Data { x.ref; }
        fn lease[perm P](given self, x: P Data) -> mut[x] Data
        where P is mut { x.mut; }
        fn either[perm P, perm Q](given self, x: P Data, y: Q Data) -> ref[x, y] Data
        where P is shared, Q is shared { x.ref; }
        fn either_mut[perm P, perm Q](given self, x: P Data, y: Q Data) -> mut[x, y] Data
        where P is mut, Q is mut { x.mut; }
        fn pick(given self, x: given Data, y: given Data) -> given_from[x, y] Data { x.give; }
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
    check_call("f.give.scalar()", "Int", "7");
}

#[test]
fn given_from_named_parameter() {
    check_call("f.give.take(d1.give)", "Data", "Data { n: 42 }");
}

#[test]
fn given_from_multiple_parameters() {
    check_call("f.give.pick(d1.give, d2.give)", "Data", "Data { n: 42 }");
}

#[test]
fn ref_through_ref() {
    check_call(
        "f.give.borrow[ref[d1]](d1.ref)",
        "ref[d1] Data",
        "ref [d1] Data { n: 42 }",
    );
}

#[test]
fn ref_through_receiver() {
    check_call(
        "d1.ref.borrow_self[ref[d1]]()",
        "ref[d1] Data",
        "ref [d1] Data { n: 42 }",
    );
}

#[test]
fn mut_through_mut() {
    check_call(
        "f.give.lease[mut[d1]](d1.mut)",
        "mut[d1] Data",
        "mut [d1] Data { n: 42 }",
    );
}

#[test]
fn ref_through_mut() {
    check_call(
        "f.give.borrow[mut[d1]](d1.mut)",
        "shared mut[d1] Data",
        "shared mut [d1] Data { n: 42 }",
    );
}

#[test]
fn multi_place_ref_keeps_runtime_branch() {
    check_call(
        "f.give.either[ref[d1], ref[d2]](d1.ref, d2.ref)",
        "ref[d1] Data",
        "ref [d1] Data { n: 42 }",
    );
}

#[test]
fn multi_place_mut_keeps_runtime_branch() {
    check_call(
        "f.give.either_mut[mut[d1], mut[d2]](d1.mut, d2.mut)",
        "mut[d1] Data",
        "mut [d1] Data { n: 42 }",
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
        class Data { n: Int; }
        class Container {
            data: Data;
            fn take(given self) -> given_from[self] Data { self.data.give; }
        }
        class Caller {
            fn run[perm P](P self, c: given Container) -> Data where P is shared {
                c.give.take();
            }
        }
        class Main {
            fn main(given self) -> Data {
                let caller = new Caller();
                caller.ref.run[ref[caller]](new Container(new Data(42)));
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_caller = new Caller () ;
        Output: Trace:   _1_caller = Caller {  }
        Output: Trace:   _1_caller . ref . run [ref [_1_caller]] (new Container (new Data (42))) ;
        Output: Trace:   enter Caller.run
        Output: Trace:     _2_c . give . take () ;
        Output: Trace:     enter Container.take
        Output: Trace:       _3_self . data . give ;
        Output: Trace:     exit Container.take => Data { n: 42 }
        Output: Trace:   exit Caller.run => Data { n: 42 }
        Output: Trace: exit Main.main => Data { n: 42 }
        Result: Ok: Data { n: 42 }
        Alloc 0x0b: [Int(42)]"#]]);
}

#[test]
fn nested_borrow_calls_preserve_value() {
    crate::assert_interpret!({
        class Data { n: Int; }
        class Funcs {
            fn borrow[perm P](given self, x: P Data) -> ref[x] Data { x.ref; }
        }
        class Main {
            fn main(given self) -> Int {
                let d = new Data(42);
                let f = new Funcs();
                let r = f.give.borrow[ref[d]](d.ref);
                let g = new Funcs();
                let s = g.give.borrow[ref[d]](r.give);
                s.n.give + 1;
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_d = new Data (42) ;
        Output: Trace:   _1_d = Data { n: 42 }
        Output: Trace:   let _1_f = new Funcs () ;
        Output: Trace:   _1_f = Funcs {  }
        Output: Trace:   let _1_r = _1_f . give . borrow [ref [_1_d]] (_1_d . ref) ;
        Output: Trace:   enter Funcs.borrow
        Output: Trace:     _2_x . ref ;
        Output: Trace:   exit Funcs.borrow => ref [_1_d] Data { n: 42 }
        Output: Trace:   _1_r = ref [_1_d] Data { n: 42 }
        Output: Trace:   let _1_g = new Funcs () ;
        Output: Trace:   _1_g = Funcs {  }
        Output: Trace:   let _1_s = _1_g . give . borrow [ref [_1_d]] (_1_r . give) ;
        Output: Trace:   enter Funcs.borrow
        Output: Trace:     _3_x . ref ;
        Output: Trace:   exit Funcs.borrow => ref [_1_d] Data { n: 42 }
        Output: Trace:   _1_s = ref [_1_d] Data { n: 42 }
        Output: Trace:   _1_s . n . give + 1 ;
        Output: Trace: exit Main.main => 43
        Result: Ok: 43
        Alloc 0x15: [Int(43)]"#]]);
}

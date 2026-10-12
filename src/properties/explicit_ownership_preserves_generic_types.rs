//! # Given preserves a generic type's permissions
//!
//! `given` is the identity permission. A bare type-variable input defaults to
//! `given T`, whether the variable belongs to its class or its method. Neither
//! spelling requires a relative bound or introduces a permission argument.
//! A nonidentity shared permission still requires the relative bound; the paired
//! declarations test that distinction through the surface pipeline.
//!
//! Instantiating `T` with `shared Data` or `![value] Data` preserves that
//! permission through a bare-`T` identity method. The complete
//! programs use the returned values: sharing remains duplicable, and a returned
//! mutable borrow can update its referent. The caller and callee deliberately
//! reuse the input name `value`, checking that type-argument origins remain in
//! the caller's scope. Dropping a referent before the returned borrow's last use
//! is rejected.
//!
//! Empty-origin shorthand `[] T` also makes the identity permission explicit
//! and requires no generated permission argument at a call.

#[test]
fn empty_origins_need_no_permission_argument() {
    crate::assert_interpret!({
        struct Main {
            fn identity(given self, value: [] Int) -> [] Int { value->; }
            fn main(given self) { print(self->identity(22)); }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   print(_1_self -> . identity (22)) ;
        Output: Trace:   enter Main.identity
        Output: Trace:     _2_value -> ;
        Output: Trace:   exit Main.identity => 22
        Output: ----->   22
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

#[test]
fn bare_and_explicit_generic_inputs_need_no_relative_bound() {
    // This checks unconstrained generic declarations; the following programs
    // exercise concrete shared and mutable instantiations at runtime.
    crate::assert_ok!({
        struct Channel[ty T] {
            fn bare_class_type(given self, value: T) { (); }
            fn explicit_class_type(given self, value: given T) { (); }
            fn bare_method_type[ty U](given self, value: U) { (); }
            fn explicit_method_type[ty U](given self, value: given U) { (); }
        }
    });
}

#[test]
fn bare_type_variable_preserves_independent_sharing() {
    crate::assert_interpret!({
        struct Data { value: Int; }
        struct Worker {
            fn identity[ty T](given self, value: T) -> T { value->; }
        }
        struct Main {
            fn main(given self) {
                let value = new Data(1).share;
                let result = new Worker().identity[shared Data](value->);
                print(result.value->);
                print(value.value->);
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_value = new Data (1) . share ;
        Output: Trace:   _1_value = shared Data { value: 1 }
        Output: Trace:   let _1_result = new Worker () . identity [shared Data] (_1_value ->) ;
        Output: Trace:   enter Worker.identity
        Output: Trace:     _2_value -> ;
        Output: Trace:   exit Worker.identity => shared Data { value: 1 }
        Output: Trace:   _1_result = shared Data { value: 1 }
        Output: Trace:   print(_1_result . value ->) ;
        Output: ----->   1
        Output: Trace:   print(_1_value . value ->) ;
        Output: ----->   1
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

#[test]
fn bare_type_variable_preserves_mutability_and_caller_origin() {
    crate::assert_interpret!({
        struct Data { value: Int; }
        struct Worker {
            fn identity[ty T](given self, value: T) -> T { value->; }
        }
        struct Main {
            fn main(given self) {
                let value = new Data(1);
                let result = new Worker().identity[![value] Data](value!);
                result.value = 7;
                print(value.value->);
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_value = new Data (1) ;
        Output: Trace:   _1_value = Data { value: 1 }
        Output: Trace:   let _1_result = new Worker () . identity [! [_1_value] Data] (_1_value !) ;
        Output: Trace:   enter Worker.identity
        Output: Trace:     _2_value -> ;
        Output: Trace:   exit Worker.identity => ! [_1_value] Data { value: 1 }
        Output: Trace:   _1_result = ! [_1_value] Data { value: 1 }
        Output: Trace:   _1_result . value = 7 ;
        Output: Trace:   _1_result . value = 7
        Output: Trace:   print(_1_value . value ->) ;
        Output: ----->   7
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

#[test]
fn returned_generic_borrow_keeps_its_referent_live() {
    crate::assert_err!({
        struct Data { value: Int; }
        struct Worker {
            fn identity[ty T](given self, value: T) -> T { value->; }
        }
        struct Main {
            fn main(given self) {
                let value = new Data(1);
                let result = new Worker().identity[![value] Data](value!);
                drop value;
                print(result.value->);
            }
        }
    }, expect_test::expect![[r#"
        the rule "lease-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, leased_place)`
            accessed_place = value
            leased_place = value"#]]);
}

#[test]
fn sharing_still_requires_a_relative_bound() {
    crate::assert_err!({
        struct Channel[ty T] {
            fn send(given self, value: shared T) { (); }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Channel [ty] { fn send (given self value : shared ^ty1_0) -> () { () ; } } }`"]);
}

//! # Signature sugar keeps calls explicit
//!
//! Receiver and input permission sugar introduce fresh permission parameters. Calls
//! supply those permissions after explicit generics, receiver first and inputs
//! left to right. Inline `ty T` declarations add type parameters at their input's
//! position in that same generated suffix, without a permission parameter for T.
//! These complete programs exercise lowering, checking, and
//! interpretation together, including dotless `!`/`->` calls; no inference fills
//! omitted arguments.

#[test]
fn explicit_type_generics_precede_receiver_and_input_permissions() {
    // This case checks generic argument ordering statically; execution is covered below.
    crate::assert_ok!({
        struct Data {}
        struct Worker {
            fn self!edit[ty T](value: !T) { (); }
        }
        struct Main {
            fn self->main() {
                // ANCHOR: explicit_generated_permission_call
                let worker = new Worker();
                let value = new Data();
                worker!edit[Data, ![worker], ![value]](value!);
                // ANCHOR_END: explicit_generated_permission_call
            }
        }
    });
}

#[test]
fn parameter_sugar_executes_with_explicit_arguments() {
    crate::assert_interpret!(
        {
        struct Data { value: Int; }
        struct Main {
            fn self.read(x: Int) -> Int { x->; }
            fn self!edit(x: !Data) { x.value = 44; }
            fn self->main() {
                let actor = new Main();
                print(actor.share.read[shared[actor], given](22));
                let data = new Data(0);
                actor!edit[![actor], ![data]](data!);
                print(data.value->);
            }
        }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let _1_actor = new Main () ;
            Output: Trace:   _1_actor = Main {  }
            Output: Trace:   print(_1_actor . share . read [shared [_1_actor], given] (22)) ;
            Output: Trace:   enter Main.read
            Output: Trace:     _2_x -> ;
            Output: Trace:   exit Main.read => 22
            Output: ----->   22
            Output: Trace:   let _1_data = new Data (0) ;
            Output: Trace:   _1_data = Data { value: 0 }
            Output: Trace:   _1_actor ! . edit [! [_1_actor], ! [_1_data]] (_1_data !) ;
            Output: Trace:   enter Main.edit
            Output: Trace:     _3_x . value = 44 ;
            Output: Trace:     _3_x . value = 44
            Output: Trace:   exit Main.edit => ()
            Output: Trace:   print(_1_data . value ->) ;
            Output: ----->   44
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

#[test]
fn omitted_generated_permission_is_rejected() {
    crate::assert_err!({
        struct Main {
            fn self.accept(x: any Int) { (); }
            fn self->main() { self!accept[![self]](1); }
        }
    }, expect_test::expect![[r#"
        the rule "class-method" at (expressions.rs) failed because
          cannot instantiate method `accept`: wrong number of parameters
          expected 2 explicit generic arguments, received 1
          generic slots (zero-based): [0: perm for receiver `self`; 1: perm for parameter `x`]
          expanded signature: fn accept[perm, perm](^perm0_0 self, x: ^perm0_1 Int) -> ()"#]]);
}

#[test]
fn wrong_kind_in_generated_slot_is_rejected() {
    crate::assert_err!({
        struct Main {
            fn self->accept[ty T](x: !T) { (); }
            fn self->main() { self->accept[Int, Int](1); }
        }
    }, expect_test::expect![[r#"
        the rule "class-method" at (expressions.rs) failed because
          cannot instantiate method `accept`: parameter 1 has kind ty but should have kind perm
          expected 2 explicit generic arguments, received 2
          generic slots (zero-based): [0: ty for parameter `x`; 1: perm for parameter `x`]
          expanded signature: fn accept[ty, perm](given self, x: ^perm0_1 ^ty0_0) -> () where [^perm0_1 is mut]"#]]);
}

#[test]
fn mutable_parameter_sugar_requires_a_mutable_permission() {
    crate::assert_err!({
        struct Data {}
        struct Main {
            fn self->edit(x: !Data) { (); }
            fn self->main() { self->edit[given](new Data()); }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn edit [perm] (given self x : ^perm0_0 Data) -> () where ^perm0_0 is mut { () ; } fn main (given self) -> () { self -> . edit [given] (new Data ()) ; } } }`"]);
}

#[test]
fn inline_types_and_permissions_follow_explicit_generics() {
    crate::assert_interpret!({
        struct Data { value: Int; }
        struct Worker {
            fn self!first[ty U](first: ty T, other: !U, last: ty V) -> T {
                first->;
            }
        }
        struct Main {
            fn self->main() {
                let worker = new Worker();
                let data = new Data(0);
                let result = worker!first[Data, ![worker], Int, ![data], Bool](22, data!, true);
                print(result->);
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_worker = new Worker () ;
        Output: Trace:   _1_worker = Worker {  }
        Output: Trace:   let _1_data = new Data (0) ;
        Output: Trace:   _1_data = Data { value: 0 }
        Output: Trace:   let _1_result = _1_worker ! . first [Data, ! [_1_worker], Int, ! [_1_data], Bool] (22, _1_data !, true) ;
        Output: Trace:   enter Worker.first
        Output: Trace:     _2_first -> ;
        Output: Trace:   exit Worker.first => 22
        Output: Trace:   _1_result = 22
        Output: Trace:   print(_1_result ->) ;
        Output: ----->   22
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

#[test]
fn inline_type_argument_cannot_be_omitted() {
    crate::assert_err!({
        struct Main {
            fn self.identity(value: ty T) -> T { value->; }
            fn self->main() { print(self!identity[![self]](22)); }
        }
    }, expect_test::expect![[r#"
        the rule "class-method" at (expressions.rs) failed because
          cannot instantiate method `identity`: wrong number of parameters
          expected 2 explicit generic arguments, received 1
          generic slots (zero-based): [0: perm for receiver `self`; 1: ty for parameter `value`]
          expanded signature: fn identity[perm, ty](^perm0_0 self, value: ^ty0_1) -> ^ty0_1"#]]);
}

#[test]
fn inline_type_argument_requires_a_type() {
    crate::assert_err!({
        struct Main {
            fn self.identity(value: ty T) -> T { value->; }
            fn self->main() { print(self!identity[![self], given](22)); }
        }
    }, expect_test::expect![[r#"
        the rule "class-method" at (expressions.rs) failed because
          cannot instantiate method `identity`: parameter 1 has kind perm but should have kind ty
          expected 2 explicit generic arguments, received 2
          generic slots (zero-based): [0: perm for receiver `self`; 1: ty for parameter `value`]
          expanded signature: fn identity[perm, ty](^perm0_0 self, value: ^ty0_1) -> ^ty0_1"#]]);
}

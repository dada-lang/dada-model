//! # Parameter permission sugar keeps calls explicit
//!
//! Bare and mutable receivers or inputs introduce fresh permission parameters. Calls
//! supply those permissions after explicit generics, receiver first and inputs
//! left to right. These complete programs exercise lowering, checking, and
//! interpretation together, including dotless `!`/`->` calls; no inference fills
//! omitted arguments.

#[test]
fn explicit_type_generics_precede_receiver_and_input_permissions() {
    // This case checks generic argument ordering statically; execution is covered below.
    crate::assert_ok!({
        struct Data {}
        struct Worker {
            fn edit[ty T](self!, value: !T) { (); }
        }
        struct Main {
            fn main(self->) {
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
            fn read(self, x: Int) -> Int { x->; }
            fn edit(self!, x: !Data) { x.value = 44; }
            fn main(self->) {
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
            fn accept(any self, x: any Int) { (); }
            fn main(self->) { self!accept[![self]](1); }
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
            fn accept[ty T](self->, x: !T) { (); }
            fn main(self->) { self->accept[Int, Int](1); }
        }
    }, expect_test::expect![[r#"
        the rule "class-method" at (expressions.rs) failed because
          cannot instantiate method `accept`: parameter 1 has kind ty but should have kind perm
          expected 2 explicit generic arguments, received 2
          generic slots (zero-based): [0: ty for parameter `x`; 1: perm for parameter `x`]
          expanded signature: fn accept[ty, perm](self->, x: ^perm0_1 ^ty0_0) -> () where [^perm0_1 is mut]"#]]);
}

#[test]
fn mutable_parameter_sugar_requires_a_mutable_permission() {
    crate::assert_err!({
        struct Data {}
        struct Main {
            fn edit(self->, x: !Data) { (); }
            fn main(self->) { self->edit[given](new Data()); }
        }
    }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Main { fn edit [perm] (self-> x : ^perm0_0 Data) -> () where ^perm0_0 is mut { () ; } fn main (self->) -> () { self -> . edit [given] (new Data ()) ; } } }`"]);
}

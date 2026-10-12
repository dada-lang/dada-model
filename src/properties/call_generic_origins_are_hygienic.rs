//! # Generic call arguments preserve caller origin identities
//!
//! Places supplied inside type or permission arguments belong to the caller.
//! Receiver, input, and local names in the callee must not capture those places,
//! including when a class generic is instantiated before a method generic.
//! These surface programs cover input-name collisions, caller `self`, projected
//! class-generic origins, crossed input names, and names resembling internal
//! temporaries. Returned permissions retain their dependency on caller storage.

#[test]
fn same_named_input_keeps_its_caller_origin_and_return_dependency() {
    crate::assert_interpret!({
        struct Data { value: Int; }
        struct Worker {
            fn forward(given self, value: !Data) -> given[value] Data { value->; }
        }
        struct Main {
            fn main(given self) {
                let worker = new Worker();
                let value = new Data(1);
                let result = worker->.forward[![value]](value!);
                result.value = 7;
                print(value.value->);
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_worker = new Worker () ;
        Output: Trace:   _1_worker = Worker {  }
        Output: Trace:   let _1_value = new Data (1) ;
        Output: Trace:   _1_value = Data { value: 1 }
        Output: Trace:   let _1_result = _1_worker -> . forward [! [_1_value]] (_1_value !) ;
        Output: Trace:   enter Worker.forward
        Output: Trace:     _2_value -> ;
        Output: Trace:   exit Worker.forward => ! [_1_value] Data { value: 1 }
        Output: Trace:   _1_result = ! [_1_value] Data { value: 1 }
        Output: Trace:   _1_result . value = 7 ;
        Output: Trace:   _1_result . value = 7
        Output: Trace:   print(_1_value . value ->) ;
        Output: ----->   7
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

#[test]
fn caller_self_is_not_the_callee_receiver_origin() {
    crate::assert_interpret!({
        struct Data {
            value: Int;
            fn set(!self) { self.value = 8; }
            fn forward(!self) { self!.set[![self]](); print(self.value->); }
        }
        struct Main {
            fn main(given self) {
                let data = new Data(1);
                data!.forward[![data]]();
                print(data.value->);
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_data = new Data (1) ;
        Output: Trace:   _1_data = Data { value: 1 }
        Output: Trace:   _1_data ! . forward [! [_1_data]] () ;
        Output: Trace:   enter Data.forward
        Output: Trace:     _2_self ! . set [! [_2_self]] () ;
        Output: Trace:     enter Data.set
        Output: Trace:       _3_self . value = 8 ;
        Output: Trace:       _3_self . value = 8
        Output: Trace:     exit Data.set => ()
        Output: Trace:     print(_2_self . value ->) ;
        Output: ----->     8
        Output: Trace:   exit Data.forward => ()
        Output: Trace:   print(_1_data . value ->) ;
        Output: ----->   8
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

#[test]
fn class_generic_projected_origins_survive_input_renaming() {
    crate::assert_interpret!({
        struct Data { value: Int; }
        struct Container { inner: Data; }
        struct Worker[perm P] {
            fn forward(self, value: P Data) -> P Data where P is shared { value->; }
        }
        struct Main {
            fn main(given self) {
                let value = new Container(new Data(1));
                let worker = new Worker[shared[value.inner]]();
                let result = worker.forward[shared[worker]](value.inner);
                print(result.value->);
                print(value.inner.value->);
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_value = new Container (new Data (1)) ;
        Output: Trace:   _1_value = Container { inner: Data { value: 1 } }
        Output: Trace:   let _1_worker = new Worker [shared [_1_value . inner]] () ;
        Output: Trace:   _1_worker = Worker {  }
        Output: Trace:   let _1_result = _1_worker . share . forward [shared [_1_worker]] (_1_value . inner . share) ;
        Output: Trace:   enter Worker.forward
        Output: Trace:     _2_value -> ;
        Output: Trace:   exit Worker.forward => shared [_1_value . inner] Data { value: 1 }
        Output: Trace:   _1_result = shared [_1_value . inner] Data { value: 1 }
        Output: Trace:   print(_1_result . value ->) ;
        Output: ----->   1
        Output: Trace:   print(_1_value . inner . value ->) ;
        Output: ----->   1
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

#[test]
fn crossed_input_names_and_placeholder_like_names_remain_distinct() {
    crate::assert_interpret!({
        struct Data { value: Int; }
        struct Worker {
            fn edit(given self, x: !Data, caller_origin_0: !Data) {
                x.value = 10;
                caller_origin_0.value = 11;
            }
        }
        struct Main {
            fn main(given self) {
                let caller_origin_0 = new Data(1);
                let x = new Data(2);
                new Worker().edit[![caller_origin_0], ![x]](caller_origin_0!, x!);
                print(caller_origin_0.value->);
                print(x.value->);
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_caller_origin_0 = new Data (1) ;
        Output: Trace:   _1_caller_origin_0 = Data { value: 1 }
        Output: Trace:   let _1_x = new Data (2) ;
        Output: Trace:   _1_x = Data { value: 2 }
        Output: Trace:   new Worker () . edit [! [_1_caller_origin_0], ! [_1_x]] (_1_caller_origin_0 !, _1_x !) ;
        Output: Trace:   enter Worker.edit
        Output: Trace:     _2_x . value = 10 ;
        Output: Trace:     _2_x . value = 10
        Output: Trace:     _2_caller_origin_0 . value = 11 ;
        Output: Trace:     _2_caller_origin_0 . value = 11
        Output: Trace:   exit Worker.edit => ()
        Output: Trace:   print(_1_caller_origin_0 . value ->) ;
        Output: ----->   10
        Output: Trace:   print(_1_x . value ->) ;
        Output: ----->   11
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

#[test]
fn runtime_local_names_do_not_capture_instantiated_generic_origins() {
    crate::assert_interpret!({
        struct Data { value: Int; }
        struct Worker {
            fn identity[perm P](given self, input: P Data) -> P Data where P is mut { input->; }
            fn forward[perm P](given self, _1_value: P Data) -> P Data where P is mut {
                new Worker().identity[P](_1_value->);
            }
        }
        struct Main {
            fn main(given self) {
                let value = new Data(1);
                let result = new Worker().forward[![value]](value!);
                result.value = 12;
                print(value.value->);
            }
        }
    }, expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_value = new Data (1) ;
        Output: Trace:   _1_value = Data { value: 1 }
        Output: Trace:   let _1_result = new Worker () . forward [! [_1_value]] (_1_value !) ;
        Output: Trace:   enter Worker.forward
        Output: Trace:     new Worker () . identity [! [_1_value]] (_2__1_value ->) ;
        Output: Trace:     enter Worker.identity
        Output: Trace:       _3_input -> ;
        Output: Trace:     exit Worker.identity => ! [_1_value] Data { value: 1 }
        Output: Trace:   exit Worker.forward => ! [_1_value] Data { value: 1 }
        Output: Trace:   _1_result = ! [_1_value] Data { value: 1 }
        Output: Trace:   _1_result . value = 12 ;
        Output: Trace:   _1_result . value = 12
        Output: Trace:   print(_1_value . value ->) ;
        Output: ----->   12
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]);
}

#[test]
fn returned_caller_origin_stays_borrowed() {
    crate::assert_err!({
        struct Data { value: Int; }
        struct Worker {
            fn forward[perm P](given self, value: P Data) -> P Data { value->; }
        }
        struct Main {
            fn main(given self) {
                let value = new Data(1);
                let result = new Worker().forward[shared[value]](value);
                value.value = 13;
                print(result.value->);
            }
        }
    }, expect_test::expect![[r#"
        the rule "share-mutation" at (accesses.rs) failed because
          condition evaluted to false: `place_disjoint_from(accessed_place, shared_place)`
            accessed_place = value . value
            shared_place = value"#]]);
}

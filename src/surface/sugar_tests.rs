use crate::surface;

#[test]
fn sigil_calls_lower_to_dotted_core_calls_with_explicit_permissions() {
    crate::assert_desugars!({
        struct Data {}
        struct Worker {
            fn edit[ty T](self!, value: !T) { (); }
            fn take(self->, value: given Data) -> given Data { value->; }
            fn demo(self->) {
                let worker = new Worker();
                let value = new Data();
                worker!edit[Data, ![worker], ![value]](value!);
                worker->take(value->);
            }
        }
    } => {
        struct Data {}
        struct Worker {
            fn edit[ty T, perm Receiver, perm Input](Receiver self, value: Input T)
                where Receiver is mut, Input is mut { (); }
            fn take(self->, value: given Data) -> given Data { value->; }
            fn demo(self->) {
                let worker = new Worker();
                let value = new Data();
                worker!.edit[Data, ![worker], ![value]](value!);
                worker->.take(value->);
            }
        }
    });
}

#[test]
fn origin_shorthand_is_explicit_even_with_empty_origins() {
    crate::assert_desugars!({
        struct Wrapper[ty T] {
            field: Array[[] T];
            fn method(self->, owner: [] T, from: [self] T, implicit: T) -> [from] T ...;
        }
    } => {
        struct Wrapper[ty T] {
            field: Array[given T];
            fn method[perm P](self->, owner: given T, from: given[self] T, implicit: P T)
                -> given[from] T ...;
        }
    });
}

#[test]
fn documented_signature_desugars_to_explicit_core() {
    crate::assert_desugars!({
        // ANCHOR: surface_generic_permission_example
        struct Worker {
            fn edit[ty T](self!, value: !T) { (); }
        }
        // ANCHOR_END: surface_generic_permission_example
    } => {
        // ANCHOR: core_generic_permission_example
        struct Worker {
            fn edit[ty T, perm Receiver, perm Input](Receiver self, value: Input T)
            where Receiver is mut, Input is mut { (); }
        }
        // ANCHOR_END: core_generic_permission_example
    });
}

#[test]
fn generated_permissions_follow_explicit_generics_receiver_first() {
    crate::assert_desugars!({
        struct Container[ty T, perm P] where T is struct {
            value: P T;
            fn method[ty U, perm Q](self!, x: any T, y: !U, z: Q U) -> P T
                where Q is owned { self.share.other[P, Q](x->, y->, z->); }
        }
    } => {
        struct Container[ty T, perm P] where T is struct {
            value: P T;
            fn method[ty U, perm Q, perm R, perm S, perm V](R self, x: S T, y: V U, z: Q U) -> P T
                where Q is owned, R is mut, V is mut { self.share.other[P, Q](x->, y->, z->); }
        }
    });
}

#[test]
fn explicit_sugar_introduces_one_outer_permission_only() {
    crate::assert_desugars!({
        struct Data {
            fn method(any self, x: any Array[Int], y: !Array[Int]) -> Array[Int] ...;
        }
    } => {
        struct Data {
            fn method[perm R, perm P, perm Q](R self, x: P Array[Int], y: Q Array[Int]) -> Array[Int]
                where Q is mut ...;
        }
    });
}

#[test]
fn sugar_is_not_accepted_in_fields_returns_or_nested_types() {
    for source in [
        "struct Data { x: any Int; }",
        "struct Data { x: !Int; }",
        "struct Data { fn method(self->) -> any Int ...; }",
        "struct Data { fn method(self->) -> !Int ...; }",
        "struct Data { fn method(self->, x: Array[any Int]) ...; }",
        "struct Data { fn method(self->, x: Array[!Int]) ...; }",
    ] {
        assert!(surface::parse_program(source).is_err(), "{source}");
    }
}

#[test]
fn permission_arguments_are_preserved_without_inference() {
    crate::assert_desugars!({
        struct Data {
            fn method[ty T](any self, x: any T) { x->; }
            fn caller(self->) { self.share.method[Int, shared[self], given](1); }
        }
    } => {
        struct Data {
            fn method[ty T, perm R, perm P](R self, x: P T) { x->; }
            fn caller(self->) { self.share.method[Int, shared[self], given](1); }
        }
    });
}

#[test]
fn omitted_outer_permissions_match_any_including_receivers() {
    crate::assert_desugars!({
        struct Data[ty T] where T is struct {
            field: Array[T];
            fn method[perm Q](self, x: Array[T], y: Q T, z: given T) -> Array[T] ...;
        }
    } => {
        struct Data[ty T] where T is struct {
            field: Array[T];
            fn method[perm Q, perm R, perm P](R self, x: P Array[T], y: Q T, z: given T) -> Array[T] ...;
        }
    });
}

#[test]
fn bare_type_parameters_gain_only_an_outer_permission() {
    crate::assert_desugars!({
        struct Data {
            fn method[ty T](self->, x: T, y: Array[T]) -> T ...;
        }
    } => {
        struct Data {
            fn method[ty T, perm P, perm Q](self->, x: P T, y: Q Array[T]) -> T ...;
        }
    });
}

#[test]
#[should_panic(expected = "surface program did not desugar to expected core")]
fn desugaring_assertion_detects_a_missing_mutable_constraint() {
    crate::assert_desugars!(
        "struct Data { fn method(self!) ...; }" =>
        "struct Data { fn method[perm P](P self) ...; }"
    );
}

#[test]
#[should_panic(expected = "expected core program did not parse")]
fn desugaring_expectation_cannot_use_surface_sugar() {
    crate::assert_desugars!({
        struct Data { fn method(self!) ...; }
    } => {
        struct Data { fn method(self!) ...; }
    });
}

use crate::surface;

#[test]
fn sigil_calls_lower_to_dotted_core_calls_with_explicit_permissions() {
    crate::assert_desugars!(r#"
        struct Data {}
        struct Worker {
            fn self!edit[type T](value: !T) { (); }
            fn take(given self, value: given Data) → given Data { value→; }
            fn demo(given self) {
                let worker = new Worker();
                let value = new Data();
                worker!edit[Data, ![worker], ![value]](value!);
                worker→take(value→);
            }
        }
    "# => r#"
        struct Data {}
        struct Worker {
            fn edit[type T, perm Receiver, perm Input](Receiver self, value: Input T)
                where Receiver is mut, Input is mut { (); }
            fn take(given self, value: given Data) → given Data { value→; }
            fn demo(given self) {
                let worker = new Worker();
                let value = new Data();
                worker!.edit[Data, ![worker], ![value]](value!);
                worker→.take(value→);
            }
        }
    "#);
}

#[test]
fn origin_shorthand_is_explicit_even_with_empty_origins() {
    crate::assert_desugars!(r#"
        struct Wrapper[type T] {
            field: Array[[] T];
            fn method(given self, owner: [] T, from: [self] T, implicit: T) → [from] T ...;
        }
    "# => r#"
        struct Wrapper[type T] {
            field: Array[given T];
            fn method(given self, owner: given T, from: given[self] T, implicit: T)
                → given[from] T ...;
        }
    "#);
}

#[test]
fn documented_signature_desugars_to_explicit_core() {
    crate::assert_desugars!(r#"
        // ANCHOR: surface_generic_permission_example
        struct Worker {
            fn self!edit[type T](value: !T) { (); }
        }
        // ANCHOR_END: surface_generic_permission_example
    "# => r#"
        // ANCHOR: core_generic_permission_example
        struct Worker {
            fn edit[type T, perm Receiver, perm Input](Receiver self, value: Input T)
            where Receiver is mut, Input is mut { (); }
        }
        // ANCHOR_END: core_generic_permission_example
    "#);
}

#[test]
fn generated_permissions_follow_explicit_generics_receiver_first() {
    crate::assert_desugars!(r#"
        struct Container[type T, perm P] where T is struct {
            value: P T;
            fn self!method[type U, perm Q](x: any T, y: !U, z: Q U) → P T
                where Q is owned { self.share.other[P, Q](x→, y→, z→); }
        }
    "# => r#"
        struct Container[type T, perm P] where T is struct {
            value: P T;
            fn method[type U, perm Q, perm R, perm S, perm V](R self, x: S T, y: V U, z: Q U) → P T
                where Q is owned, R is mut, V is mut { self.share.other[P, Q](x→, y→, z→); }
        }
    "#);
}

#[test]
fn explicit_sugar_introduces_one_outer_permission_only() {
    crate::assert_desugars!(r#"
        struct Data {
            fn self.method(x: any Array[Int], y: !Array[Int]) → Array[Int] ...;
        }
    "# => r#"
        struct Data {
            fn method[perm R, perm P, perm Q](R self, x: P Array[Int], y: Q Array[Int]) → Array[Int]
                where Q is mut ...;
        }
    "#);
}

#[test]
fn sugar_is_not_accepted_in_fields_returns_or_nested_types() {
    for source in [
        "struct Data { x: any Int; }",
        "struct Data { x: !Int; }",
        "struct Data { fn method(given self) → any Int ...; }",
        "struct Data { fn method(given self) → !Int ...; }",
        "struct Data { fn method(given self, x: Array[any Int]) ...; }",
        "struct Data { fn method(given self, x: Array[!Int]) ...; }",
    ] {
        assert!(surface::parse_program(source).is_err(), "{source}");
    }
}

#[test]
fn permission_arguments_are_preserved_without_inference() {
    crate::assert_desugars!(r#"
        struct Data {
            fn self.method[type T](x: any T) { x→; }
            fn caller(given self) { self.share.method[Int, shared[self], given](1); }
        }
    "# => r#"
        struct Data {
            fn method[type T, perm R, perm P](R self, x: P T) { x→; }
            fn caller(given self) { self.share.method[Int, shared[self], given](1); }
        }
    "#);
}

#[test]
fn omitted_outer_permissions_match_any_including_receivers() {
    crate::assert_desugars!(r#"
        struct Data[type T] where T is struct {
            field: Array[T];
            fn self.method[perm Q](x: Array[T], y: Q T, z: given T) → Array[T] ...;
        }
    "# => r#"
        struct Data[type T] where T is struct {
            field: Array[T];
            fn method[perm Q, perm R, perm P](R self, x: P Array[T], y: Q T, z: given T) → Array[T] ...;
        }
    "#);
}

#[test]
fn bare_type_parameters_preserve_the_type_argument() {
    crate::assert_desugars!(r#"
        struct Data {
            fn method[type T](given self, x: T, y: Array[T]) → T ...;
        }
    "# => r#"
        struct Data {
            fn method[type T, perm P](given self, x: T, y: P Array[T]) → T ...;
        }
    "#);
}

#[test]
#[should_panic(expected = "surface program did not desugar to expected core")]
fn desugaring_assertion_detects_a_missing_mutable_constraint() {
    crate::assert_desugars!(
        "struct Data { fn self!method() ...; }" =>
        "struct Data { fn method[perm P](P self) ...; }"
    );
}

#[test]
#[should_panic(expected = "expected core program did not parse")]
fn desugaring_expectation_cannot_use_surface_sugar() {
    crate::assert_desugars!(r#"
        struct Data { fn self!method() ...; }
    "# => r#"
        struct Data { fn self!method() ...; }
    "#);
}

use formality_core::test;

#[test]
fn given_and_shared_satisfy_owned() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container { field: Wrapper; }
        struct Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Container, source2: ^ Container,
                    d1: ^ Container, d2: shared Container,
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_owned[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn shared_and_given_satisfy_owned() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container { field: Wrapper; }
        struct Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Container, source2: ^ Container,
                    d1: shared Container, d2: ^ Container,
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_owned[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn given_and_ref_do_not_satisfy_owned() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container { field: Wrapper; }
        struct Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Container, source2: ^ Container,
                    d1: ^ Container, d2: shared[source2] Container,
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_owned[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container { field : Wrapper ; } struct Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Container, source2 : ^ Container, d1 : ^ Container, d2 : shared [source2] Container, x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_owned [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn ref_and_given_do_not_satisfy_owned() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container { field: Wrapper; }
        struct Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Container, source2: ^ Container,
                    d1: shared[source1] Container, d2: ^ Container,
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_owned[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container { field : Wrapper ; } struct Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Container, source2 : ^ Container, d1 : shared [source1] Container, d2 : ^ Container, x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_owned [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn shared_and_mut_do_not_satisfy_owned() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container { field: Wrapper; }
        struct Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Container, source2: ^ Container,
                    d1: shared Container, d2: ![source2] Container,
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_owned[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container { field : Wrapper ; } struct Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Container, source2 : ^ Container, d1 : shared Container, d2 : ! [source2] Container, x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_owned [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn mut_and_shared_do_not_satisfy_owned() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container { field: Wrapper; }
        struct Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Container, source2: ^ Container,
                    d1: ![source1] Container, d2: shared Container,
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_owned[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container { field : Wrapper ; } struct Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Container, source2 : ^ Container, d1 : ! [source1] Container, d2 : shared Container, x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_owned [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

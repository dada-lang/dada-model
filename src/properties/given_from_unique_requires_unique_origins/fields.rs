use formality_core::test;

#[test]
fn given_and_mut_satisfy_unique() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container { field: Wrapper; }
        struct Main {
            fn require_unique[perm P](given self, value: P Wrapper)
            where P is unique { (); }

            fn test(given self,
                    source1: given Container, source2: given Container,
                    d1: given Container, d2: ![source2] Container,
                    x: given[d1.field, d2.field] Wrapper) {
                self^.require_unique[given[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn mut_and_given_satisfy_unique() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container { field: Wrapper; }
        struct Main {
            fn require_unique[perm P](given self, value: P Wrapper)
            where P is unique { (); }

            fn test(given self,
                    source1: given Container, source2: given Container,
                    d1: ![source1] Container, d2: given Container,
                    x: given[d1.field, d2.field] Wrapper) {
                self^.require_unique[given[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn given_and_shared_do_not_satisfy_unique() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container { field: Wrapper; }
        struct Main {
            fn require_unique[perm P](given self, value: P Wrapper)
            where P is unique { (); }

            fn test(given self,
                    source1: given Container, source2: given Container,
                    d1: given Container, d2: shared Container,
                    x: given[d1.field, d2.field] Wrapper) {
                self^.require_unique[given[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the unique requirement is removed.
    crate::assert_ok!(&program.replace("where P is unique", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container { field : Wrapper ; } struct Main { fn require_unique [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is unique { () ; } fn test (given self source1 : given Container, source2 : given Container, d1 : given Container, d2 : shared Container, x : given [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_unique [given [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn shared_and_given_do_not_satisfy_unique() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container { field: Wrapper; }
        struct Main {
            fn require_unique[perm P](given self, value: P Wrapper)
            where P is unique { (); }

            fn test(given self,
                    source1: given Container, source2: given Container,
                    d1: shared Container, d2: given Container,
                    x: given[d1.field, d2.field] Wrapper) {
                self^.require_unique[given[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the unique requirement is removed.
    crate::assert_ok!(&program.replace("where P is unique", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container { field : Wrapper ; } struct Main { fn require_unique [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is unique { () ; } fn test (given self source1 : given Container, source2 : given Container, d1 : shared Container, d2 : given Container, x : given [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_unique [given [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn mut_and_ref_do_not_satisfy_unique() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container { field: Wrapper; }
        struct Main {
            fn require_unique[perm P](given self, value: P Wrapper)
            where P is unique { (); }

            fn test(given self,
                    source1: given Container, source2: given Container,
                    d1: ![source1] Container, d2: shared[source2] Container,
                    x: given[d1.field, d2.field] Wrapper) {
                self^.require_unique[given[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the unique requirement is removed.
    crate::assert_ok!(&program.replace("where P is unique", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container { field : Wrapper ; } struct Main { fn require_unique [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is unique { () ; } fn test (given self source1 : given Container, source2 : given Container, d1 : ! [source1] Container, d2 : shared [source2] Container, x : given [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_unique [given [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn ref_and_mut_do_not_satisfy_unique() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container { field: Wrapper; }
        struct Main {
            fn require_unique[perm P](given self, value: P Wrapper)
            where P is unique { (); }

            fn test(given self,
                    source1: given Container, source2: given Container,
                    d1: shared[source1] Container, d2: ![source2] Container,
                    x: given[d1.field, d2.field] Wrapper) {
                self^.require_unique[given[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the unique requirement is removed.
    crate::assert_ok!(&program.replace("where P is unique", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container { field : Wrapper ; } struct Main { fn require_unique [perm] (given self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is unique { () ; } fn test (given self source1 : given Container, source2 : given Container, d1 : shared [source1] Container, d2 : ! [source2] Container, x : given [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_unique [given [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

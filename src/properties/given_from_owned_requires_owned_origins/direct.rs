use formality_core::test;

#[test]
fn given_and_given_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Wrapper, d2: ^ Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self^.require_owned[^[d1, d2]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn given_and_mut_do_not_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Wrapper, d2: ![source2] Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self^.require_owned[^[d1, d2]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Wrapper, d2 : ! [source2] Wrapper, x : ^ [d1, d2] Wrapper) -> () { self ^ . require_owned [^ [d1, d2]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn given_and_shared_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Wrapper, d2: shared Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self^.require_owned[^[d1, d2]](x^);
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
        class Wrapper { value: Int; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Wrapper, d2: shared[source2] Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self^.require_owned[^[d1, d2]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Wrapper, d2 : shared [source2] Wrapper, x : ^ [d1, d2] Wrapper) -> () { self ^ . require_owned [^ [d1, d2]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn mut_and_given_do_not_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ![source1] Wrapper, d2: ^ Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self^.require_owned[^[d1, d2]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ! [source1] Wrapper, d2 : ^ Wrapper, x : ^ [d1, d2] Wrapper) -> () { self ^ . require_owned [^ [d1, d2]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn mut_and_mut_do_not_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ![source1] Wrapper, d2: ![source2] Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self^.require_owned[^[d1, d2]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ! [source1] Wrapper, d2 : ! [source2] Wrapper, x : ^ [d1, d2] Wrapper) -> () { self ^ . require_owned [^ [d1, d2]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn mut_and_shared_do_not_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ![source1] Wrapper, d2: shared Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self^.require_owned[^[d1, d2]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ! [source1] Wrapper, d2 : shared Wrapper, x : ^ [d1, d2] Wrapper) -> () { self ^ . require_owned [^ [d1, d2]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn mut_and_ref_do_not_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ![source1] Wrapper, d2: shared[source2] Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self^.require_owned[^[d1, d2]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ! [source1] Wrapper, d2 : shared [source2] Wrapper, x : ^ [d1, d2] Wrapper) -> () { self ^ . require_owned [^ [d1, d2]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn shared_and_given_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: shared Wrapper, d2: ^ Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self^.require_owned[^[d1, d2]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn shared_and_mut_do_not_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: shared Wrapper, d2: ![source2] Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self^.require_owned[^[d1, d2]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : shared Wrapper, d2 : ! [source2] Wrapper, x : ^ [d1, d2] Wrapper) -> () { self ^ . require_owned [^ [d1, d2]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn shared_and_shared_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: shared Wrapper, d2: shared Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self^.require_owned[^[d1, d2]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn shared_and_ref_do_not_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: shared Wrapper, d2: shared[source2] Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self^.require_owned[^[d1, d2]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : shared Wrapper, d2 : shared [source2] Wrapper, x : ^ [d1, d2] Wrapper) -> () { self ^ . require_owned [^ [d1, d2]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn ref_and_given_do_not_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: shared[source1] Wrapper, d2: ^ Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self^.require_owned[^[d1, d2]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : shared [source1] Wrapper, d2 : ^ Wrapper, x : ^ [d1, d2] Wrapper) -> () { self ^ . require_owned [^ [d1, d2]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn ref_and_mut_do_not_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: shared[source1] Wrapper, d2: ![source2] Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self^.require_owned[^[d1, d2]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : shared [source1] Wrapper, d2 : ! [source2] Wrapper, x : ^ [d1, d2] Wrapper) -> () { self ^ . require_owned [^ [d1, d2]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn ref_and_shared_do_not_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: shared[source1] Wrapper, d2: shared Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self^.require_owned[^[d1, d2]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : shared [source1] Wrapper, d2 : shared Wrapper, x : ^ [d1, d2] Wrapper) -> () { self ^ . require_owned [^ [d1, d2]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn ref_and_ref_do_not_satisfy_owned() {
    let program = r#"
        class Wrapper { value: Int; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: shared[source1] Wrapper, d2: shared[source2] Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self^.require_owned[^[d1, d2]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : shared [source1] Wrapper, d2 : shared [source2] Wrapper, x : ^ [d1, d2] Wrapper) -> () { self ^ . require_owned [^ [d1, d2]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn references_to_owned_shared_values_can_be_owned() {
    crate::assert_ok!({
        class Wrapper { value: Int; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self, source: shared Wrapper, other: shared Wrapper) {
                let d1: shared[source] Wrapper = source.share;
                let x: ^[d1, other] Wrapper = d1^;
                self^.require_owned[^[d1, other]](x^);
                source.share;
                other.share;
                ();
            }
        }
    });
}

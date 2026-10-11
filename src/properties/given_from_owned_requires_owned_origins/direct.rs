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
                self.give.require_owned[^[d1, d2]](x.give);
                source1.ref;
                source2.ref;
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
                    d1: ^ Wrapper, d2: mut[source2] Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self.give.require_owned[^[d1, d2]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Wrapper, d2 : mut [source2] Wrapper, x : ^ [d1, d2] Wrapper) -> () { self . give . require_owned [^ [d1, d2]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
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
                self.give.require_owned[^[d1, d2]](x.give);
                source1.ref;
                source2.ref;
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
                    d1: ^ Wrapper, d2: ref[source2] Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self.give.require_owned[^[d1, d2]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Wrapper, d2 : ref [source2] Wrapper, x : ^ [d1, d2] Wrapper) -> () { self . give . require_owned [^ [d1, d2]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
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
                    d1: mut[source1] Wrapper, d2: ^ Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self.give.require_owned[^[d1, d2]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : mut [source1] Wrapper, d2 : ^ Wrapper, x : ^ [d1, d2] Wrapper) -> () { self . give . require_owned [^ [d1, d2]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
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
                    d1: mut[source1] Wrapper, d2: mut[source2] Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self.give.require_owned[^[d1, d2]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : mut [source1] Wrapper, d2 : mut [source2] Wrapper, x : ^ [d1, d2] Wrapper) -> () { self . give . require_owned [^ [d1, d2]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
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
                    d1: mut[source1] Wrapper, d2: shared Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self.give.require_owned[^[d1, d2]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : mut [source1] Wrapper, d2 : shared Wrapper, x : ^ [d1, d2] Wrapper) -> () { self . give . require_owned [^ [d1, d2]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
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
                    d1: mut[source1] Wrapper, d2: ref[source2] Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self.give.require_owned[^[d1, d2]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : mut [source1] Wrapper, d2 : ref [source2] Wrapper, x : ^ [d1, d2] Wrapper) -> () { self . give . require_owned [^ [d1, d2]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
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
                self.give.require_owned[^[d1, d2]](x.give);
                source1.ref;
                source2.ref;
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
                    d1: shared Wrapper, d2: mut[source2] Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self.give.require_owned[^[d1, d2]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : shared Wrapper, d2 : mut [source2] Wrapper, x : ^ [d1, d2] Wrapper) -> () { self . give . require_owned [^ [d1, d2]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
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
                self.give.require_owned[^[d1, d2]](x.give);
                source1.ref;
                source2.ref;
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
                    d1: shared Wrapper, d2: ref[source2] Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self.give.require_owned[^[d1, d2]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : shared Wrapper, d2 : ref [source2] Wrapper, x : ^ [d1, d2] Wrapper) -> () { self . give . require_owned [^ [d1, d2]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
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
                    d1: ref[source1] Wrapper, d2: ^ Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self.give.require_owned[^[d1, d2]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ref [source1] Wrapper, d2 : ^ Wrapper, x : ^ [d1, d2] Wrapper) -> () { self . give . require_owned [^ [d1, d2]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
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
                    d1: ref[source1] Wrapper, d2: mut[source2] Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self.give.require_owned[^[d1, d2]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ref [source1] Wrapper, d2 : mut [source2] Wrapper, x : ^ [d1, d2] Wrapper) -> () { self . give . require_owned [^ [d1, d2]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
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
                    d1: ref[source1] Wrapper, d2: shared Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self.give.require_owned[^[d1, d2]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ref [source1] Wrapper, d2 : shared Wrapper, x : ^ [d1, d2] Wrapper) -> () { self . give . require_owned [^ [d1, d2]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
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
                    d1: ref[source1] Wrapper, d2: ref[source2] Wrapper,
                    x: ^[d1, d2] Wrapper) {
                self.give.require_owned[^[d1, d2]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the owned requirement is removed.
    crate::assert_ok!(&program.replace("where P is owned", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Main { fn require_owned [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is owned { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ref [source1] Wrapper, d2 : ref [source2] Wrapper, x : ^ [d1, d2] Wrapper) -> () { self . give . require_owned [^ [d1, d2]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn references_to_owned_shared_values_can_be_owned() {
    crate::assert_ok!({
        class Wrapper { value: Int; }
        class Main {
            fn require_owned[perm P](^ self, value: P Wrapper)
            where P is owned { (); }

            fn test(^ self, source: shared Wrapper, other: shared Wrapper) {
                let d1: ref[source] Wrapper = source.ref;
                let x: ^[d1, other] Wrapper = d1.give;
                self.give.require_owned[^[d1, other]](x.give);
                source.ref;
                other.ref;
                ();
            }
        }
    });
}

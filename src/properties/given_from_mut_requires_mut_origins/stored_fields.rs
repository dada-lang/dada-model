use formality_core::test;

#[test]
fn given_and_given_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[^], d2: ^ Container[^],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[^], d2 : ^ Container[^], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn given_and_mut_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[^], d2: ^ Container[![source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[^], d2 : ^ Container[! [source2]], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn given_and_shared_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[^], d2: ^ Container[shared],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[^], d2 : ^ Container[shared], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn given_and_ref_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[^], d2: ^ Container[shared[source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[^], d2 : ^ Container[shared [source2]], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn mut_and_given_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[![source1]], d2: ^ Container[^],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[! [source1]], d2 : ^ Container[^], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn mut_and_mut_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[![source1]], d2: ^ Container[![source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn mut_and_shared_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[![source1]], d2: ^ Container[shared],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[! [source1]], d2 : ^ Container[shared], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn mut_and_ref_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[![source1]], d2: ^ Container[shared[source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[! [source1]], d2 : ^ Container[shared [source2]], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn shared_and_given_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared], d2: ^ Container[^],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[shared], d2 : ^ Container[^], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn shared_and_mut_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared], d2: ^ Container[![source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[shared], d2 : ^ Container[! [source2]], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn shared_and_shared_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared], d2: ^ Container[shared],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[shared], d2 : ^ Container[shared], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn shared_and_ref_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared], d2: ^ Container[shared[source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[shared], d2 : ^ Container[shared [source2]], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn ref_and_given_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared[source1]], d2: ^ Container[^],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[shared [source1]], d2 : ^ Container[^], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn ref_and_mut_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared[source1]], d2: ^ Container[![source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[shared [source1]], d2 : ^ Container[! [source2]], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn ref_and_shared_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared[source1]], d2: ^ Container[shared],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[shared [source1]], d2 : ^ Container[shared], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn ref_and_ref_do_not_satisfy_mut() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container[perm P] { field: P Wrapper; }
        class Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared[source1]], d2: ^ Container[shared[source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container [perm] { field : ^perm0_0 Wrapper ; } class Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[shared [source1]], d2 : ^ Container[shared [source2]], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

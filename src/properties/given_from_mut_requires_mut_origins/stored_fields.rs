use formality_core::test;

#[test]
fn given_and_given_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[^], d2: ^ Container[^],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[^], d2 : ^ Container[^], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn given_and_mut_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[^], d2: ^ Container[![source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[^], d2 : ^ Container[! [source2]], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn given_and_shared_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[^], d2: ^ Container[shared],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[^], d2 : ^ Container[shared], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn given_and_ref_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[^], d2: ^ Container[shared[source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[^], d2 : ^ Container[shared [source2]], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn mut_and_given_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[![source1]], d2: ^ Container[^],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[! [source1]], d2 : ^ Container[^], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn mut_and_mut_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[![source1]], d2: ^ Container[![source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn mut_and_shared_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[![source1]], d2: ^ Container[shared],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[! [source1]], d2 : ^ Container[shared], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn mut_and_ref_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[![source1]], d2: ^ Container[shared[source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[! [source1]], d2 : ^ Container[shared [source2]], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn shared_and_given_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared], d2: ^ Container[^],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[shared], d2 : ^ Container[^], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn shared_and_mut_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared], d2: ^ Container[![source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[shared], d2 : ^ Container[! [source2]], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn shared_and_shared_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared], d2: ^ Container[shared],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[shared], d2 : ^ Container[shared], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn shared_and_ref_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared], d2: ^ Container[shared[source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[shared], d2 : ^ Container[shared [source2]], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn ref_and_given_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared[source1]], d2: ^ Container[^],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[shared [source1]], d2 : ^ Container[^], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn ref_and_mut_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared[source1]], d2: ^ Container[![source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[shared [source1]], d2 : ^ Container[! [source2]], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn ref_and_shared_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared[source1]], d2: ^ Container[shared],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[shared [source1]], d2 : ^ Container[shared], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

#[test]
fn ref_and_ref_do_not_satisfy_mut() {
    let program = r#"
        struct Wrapper { value: Int; }
        struct Container[perm P] { field: P Wrapper; }
        struct Main {
            fn require_mut[perm P](^ self, value: P Wrapper)
            where P is mut { (); }

            fn test(^ self,
                    source1: ^ Wrapper, source2: ^ Wrapper,
                    d1: ^ Container[shared[source1]], d2: ^ Container[shared[source2]],
                    x: ^[d1.field, d2.field] Wrapper) {
                self^.require_mut[^[d1.field, d2.field]](x^);
                source1.share;
                source2.share;
                ();
            }
        }
    "#;
    // The call is otherwise valid; only the mut requirement makes it fail.
    crate::assert_ok!(&program.replace("where P is mut", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Wrapper { value : Int ; } struct Container [perm] { field : ^perm0_0 Wrapper ; } struct Main { fn require_mut [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is mut { () ; } fn test (^ self source1 : ^ Wrapper, source2 : ^ Wrapper, d1 : ^ Container[shared [source1]], d2 : ^ Container[shared [source2]], x : ^ [d1 . field, d2 . field] Wrapper) -> () { self ^ . require_mut [^ [d1 . field, d2 . field]] (x ^) ; source1 . share ; source2 . share ; () ; } } }`"]);
}

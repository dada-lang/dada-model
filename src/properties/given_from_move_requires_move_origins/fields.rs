use formality_core::test;

#[test]
fn given_and_mut_satisfy_move() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container { field: Wrapper; }
        class Main {
            fn require_move[perm P](^ self, value: P Wrapper)
            where P is move { (); }

            fn test(^ self,
                    source1: ^ Container, source2: ^ Container,
                    d1: ^ Container, d2: ![source2] Container,
                    x: ^[d1.field, d2.field] Wrapper) {
                self.give.require_move[^[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn mut_and_given_satisfy_move() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container { field: Wrapper; }
        class Main {
            fn require_move[perm P](^ self, value: P Wrapper)
            where P is move { (); }

            fn test(^ self,
                    source1: ^ Container, source2: ^ Container,
                    d1: ![source1] Container, d2: ^ Container,
                    x: ^[d1.field, d2.field] Wrapper) {
                self.give.require_move[^[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    crate::assert_ok!(program);
}

#[test]
fn given_and_shared_do_not_satisfy_move() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container { field: Wrapper; }
        class Main {
            fn require_move[perm P](^ self, value: P Wrapper)
            where P is move { (); }

            fn test(^ self,
                    source1: ^ Container, source2: ^ Container,
                    d1: ^ Container, d2: shared Container,
                    x: ^[d1.field, d2.field] Wrapper) {
                self.give.require_move[^[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the move requirement is removed.
    crate::assert_ok!(&program.replace("where P is move", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container { field : Wrapper ; } class Main { fn require_move [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is move { () ; } fn test (^ self source1 : ^ Container, source2 : ^ Container, d1 : ^ Container, d2 : shared Container, x : ^ [d1 . field, d2 . field] Wrapper) -> () { self . give . require_move [^ [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn shared_and_given_do_not_satisfy_move() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container { field: Wrapper; }
        class Main {
            fn require_move[perm P](^ self, value: P Wrapper)
            where P is move { (); }

            fn test(^ self,
                    source1: ^ Container, source2: ^ Container,
                    d1: shared Container, d2: ^ Container,
                    x: ^[d1.field, d2.field] Wrapper) {
                self.give.require_move[^[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the move requirement is removed.
    crate::assert_ok!(&program.replace("where P is move", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container { field : Wrapper ; } class Main { fn require_move [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is move { () ; } fn test (^ self source1 : ^ Container, source2 : ^ Container, d1 : shared Container, d2 : ^ Container, x : ^ [d1 . field, d2 . field] Wrapper) -> () { self . give . require_move [^ [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn mut_and_ref_do_not_satisfy_move() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container { field: Wrapper; }
        class Main {
            fn require_move[perm P](^ self, value: P Wrapper)
            where P is move { (); }

            fn test(^ self,
                    source1: ^ Container, source2: ^ Container,
                    d1: ![source1] Container, d2: ref[source2] Container,
                    x: ^[d1.field, d2.field] Wrapper) {
                self.give.require_move[^[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the move requirement is removed.
    crate::assert_ok!(&program.replace("where P is move", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container { field : Wrapper ; } class Main { fn require_move [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is move { () ; } fn test (^ self source1 : ^ Container, source2 : ^ Container, d1 : ! [source1] Container, d2 : ref [source2] Container, x : ^ [d1 . field, d2 . field] Wrapper) -> () { self . give . require_move [^ [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

#[test]
fn ref_and_mut_do_not_satisfy_move() {
    let program = r#"
        class Wrapper { value: Int; }
        class Container { field: Wrapper; }
        class Main {
            fn require_move[perm P](^ self, value: P Wrapper)
            where P is move { (); }

            fn test(^ self,
                    source1: ^ Container, source2: ^ Container,
                    d1: ref[source1] Container, d2: ![source2] Container,
                    x: ^[d1.field, d2.field] Wrapper) {
                self.give.require_move[^[d1.field, d2.field]](x.give);
                source1.ref;
                source2.ref;
                ();
            }
        }
    "#;
    // The call is valid when only the move requirement is removed.
    crate::assert_ok!(&program.replace("where P is move", ""));
    crate::assert_err!(program, expect_test::expect!["judgment had no applicable rules: `check_program { program: class Wrapper { value : Int ; } class Container { field : Wrapper ; } class Main { fn require_move [perm] (^ self value : ^perm0_0 Wrapper) -> () where ^perm0_0 is move { () ; } fn test (^ self source1 : ^ Container, source2 : ^ Container, d1 : ref [source1] Container, d2 : ! [source2] Container, x : ^ [d1 . field, d2 . field] Wrapper) -> () { self . give . require_move [^ [d1 . field, d2 . field]] (x . give) ; source1 . ref ; source2 . ref ; () ; } } }`"]);
}

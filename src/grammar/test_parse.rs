use super::{Binder, Expr, Perm, Place, Program, Ty};
use formality_core::test;

#[test]
fn test_parse_program() {
    let p: Program = crate::dada_lang::term(
        "
        class Point {
            x: Int;
            y: Int;
        }

        fn identity(p: given Point) -> given Point {
            p.give;
        }
    ",
    );
    expect_test::expect![[r#"
        Program {
            decls: [
                ClassDecl(
                    ClassDecl {
                        name: Point,
                        binder: { x : Int ; y : Int ; },
                    },
                ),
                FnDecl(
                    FnDecl {
                        name: identity,
                        binder: (p : given Point) -> given Point { p . give ; },
                    },
                ),
            ],
        }
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_place() {
    let p: Place = crate::dada_lang::term("a.b.c");
    expect_test::expect![[r#"
        Place {
            var: a,
            projections: [
                Field(
                    b,
                ),
                Field(
                    c,
                ),
            ],
        }
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_shared_perm() {
    let p: Perm = crate::dada_lang::term("shared(a.b.c)");
    expect_test::expect![[r#"
        Shared(
            {
                Place {
                    var: a,
                    projections: [
                        Field(
                            b,
                        ),
                        Field(
                            c,
                        ),
                    ],
                },
            },
        )
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_our_perm_without_parens() {
    let p: Perm = crate::dada_lang::term("shared");
    expect_test::expect![[r#"
        Shared(
            {},
        )
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_our_perm_with_parens() {
    let p: Perm = crate::dada_lang::term("shared()");
    expect_test::expect![[r#"
        Shared(
            {},
        )
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_shared_perm_2() {
    let p: Perm = crate::dada_lang::term("shared(a,b)");
    expect_test::expect![[r#"
        Shared(
            {
                Place {
                    var: a,
                    projections: [],
                },
                Place {
                    var: b,
                    projections: [],
                },
            },
        )
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_my_perm() {
    let p: Perm = crate::dada_lang::term("given");
    expect_test::expect![[r#"
        Given(
            {},
        )
    "#]]
    .assert_debug_eq(&p);
}

#[test]
#[allow(non_snake_case)]
fn test_parse_String_ty() {
    let p: Ty = crate::dada_lang::term("shared String");
    expect_test::expect![[r#"
        ApplyPerm(
            Shared(
                {},
            ),
            ClassTy(
                ClassTy {
                    name: Id(
                        String,
                    ),
                    parameters: [],
                },
            ),
        )
    "#]]
    .assert_debug_eq(&p);
}

#[test]
#[allow(non_snake_case)]
fn test_parse_Vec_ty() {
    let p: Ty = crate::dada_lang::term("shared Vec[given U32]");
    expect_test::expect![[r#"
        ApplyPerm(
            Shared(
                {},
            ),
            ClassTy(
                ClassTy {
                    name: Id(
                        Vec,
                    ),
                    parameters: [
                        Ty(
                            ApplyPerm(
                                Given(
                                    {},
                                ),
                                ClassTy(
                                    ClassTy {
                                        name: Id(
                                            U32,
                                        ),
                                        parameters: [],
                                    },
                                ),
                            ),
                        ),
                    ],
                },
            ),
        )
    "#]]
    .assert_debug_eq(&p);
}

#[test]
fn test_parse_expr() {
    let p: Expr = crate::dada_lang::term(
        r#"
        {
            let x = foo(bar, baz);
            x = 22;
            await y;
        }
    "#,
    );
    expect_test::expect![[r#"
        Block(
            Block {
                statements: [
                    Let(
                        x,
                        Call(
                            Place(
                                Share(
                                    Place {
                                        var: foo,
                                        projections: [],
                                    },
                                ),
                            ),
                            [
                                Place(
                                    Share(
                                        Place {
                                            var: bar,
                                            projections: [],
                                        },
                                    ),
                                ),
                                Place(
                                    Share(
                                        Place {
                                            var: baz,
                                            projections: [],
                                        },
                                    ),
                                ),
                            ],
                        ),
                    ),
                    Reassign(
                        Place {
                            var: x,
                            projections: [],
                        },
                        Integer(
                            22,
                        ),
                    ),
                    Expr(
                        Await(
                            Place {
                                var: y,
                                projections: [],
                            },
                        ),
                    ),
                ],
            },
        )
    "#]]
    .assert_debug_eq(&p);
}

use super::{Expr, Perm, Place, Program, Ty};
use formality_core::test;

#[test]
fn test_parse_program() {
    let p: Program = crate::dada_lang::term(
        "
        class Point {
            x: Int;
            y: Int;

            fn identity(my self) -> my Point {
                p.give;
            }
        }
    ",
    );
    expect_test::expect![[r#"
        Program {
            decls: [
                ClassDecl(
                    ClassDecl {
                        name: Point,
                        binder: Binder {
                            kinds: [],
                            term: ClassDeclBoundData {
                                fields: [
                                    FieldDecl {
                                        atomic: No,
                                        name: x,
                                        ty: NamedTy(
                                            NamedTy {
                                                name: Int,
                                                parameters: [],
                                            },
                                        ),
                                    },
                                    FieldDecl {
                                        atomic: No,
                                        name: y,
                                        ty: NamedTy(
                                            NamedTy {
                                                name: Int,
                                                parameters: [],
                                            },
                                        ),
                                    },
                                ],
                                methods: [
                                    MethodDecl {
                                        name: identity,
                                        binder: Binder {
                                            kinds: [],
                                            term: MethodDeclBoundData {
                                                this: ThisDecl {
                                                    perm: My,
                                                },
                                                inputs: [],
                                                output: ApplyPerm(
                                                    My,
                                                    NamedTy(
                                                        NamedTy {
                                                            name: Id(
                                                                Point,
                                                            ),
                                                            parameters: [],
                                                        },
                                                    ),
                                                ),
                                                predicates: [],
                                                body: Block {
                                                    statements: [
                                                        Expr(
                                                            Place(
                                                                PlaceExpr {
                                                                    place: Place {
                                                                        var: Id(
                                                                            p,
                                                                        ),
                                                                        projections: [],
                                                                    },
                                                                    access: Give,
                                                                },
                                                            ),
                                                        ),
                                                    ],
                                                },
                                            },
                                        },
                                    },
                                ],
                            },
                        },
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
            var: Id(
                a,
            ),
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
                    var: Id(
                        a,
                    ),
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
                    var: Id(
                        a,
                    ),
                    projections: [],
                },
                Place {
                    var: Id(
                        b,
                    ),
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
            NamedTy(
                NamedTy {
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
            NamedTy(
                NamedTy {
                    name: Id(
                        Vec,
                    ),
                    parameters: [
                        Ty(
                            ApplyPerm(
                                Given(
                                    {},
                                ),
                                NamedTy(
                                    NamedTy {
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
            let x = y.share.foo(bar.share, baz.share);
            x = 22;
        }
    "#,
    );
    expect_test::expect![[r#"
        Block(
            Block {
                statements: [
                    Let(
                        x,
                        NoTy,
                        Call(
                            Place(
                                PlaceExpr {
                                    place: Place {
                                        var: Id(
                                            y,
                                        ),
                                        projections: [],
                                    },
                                    access: Share,
                                },
                            ),
                            foo,
                            [],
                            [
                                Place(
                                    PlaceExpr {
                                        place: Place {
                                            var: Id(
                                                bar,
                                            ),
                                            projections: [],
                                        },
                                        access: Share,
                                    },
                                ),
                                Place(
                                    PlaceExpr {
                                        place: Place {
                                            var: Id(
                                                baz,
                                            ),
                                            projections: [],
                                        },
                                        access: Share,
                                    },
                                ),
                            ],
                        ),
                    ),
                    Reassign(
                        Place {
                            var: Id(
                                x,
                            ),
                            projections: [],
                        },
                        Integer(
                            22,
                        ),
                    ),
                ],
            },
        )
    "#]]
    .assert_debug_eq(&p);
}

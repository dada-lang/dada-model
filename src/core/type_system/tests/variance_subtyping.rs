use formality_core::test;

#[test]
#[allow(non_snake_case)]
fn Cell_T_our_Cell_Data_to_our_Cell_our_Data() {
    crate::assert_ok!({
    struct Data {}
    struct Cell[ty T]
    {
        f: T;
    }
    struct Main {
        fn test(^ self, d1: shared Cell[Data]) -> shared Cell[shared Data] {
            d1^;
        }
    }
    });
}

#[test]
#[allow(non_snake_case)]
fn Cell_atomic_T_our_Cell_Data_to_our_Cell_our_Data() {
    // Since T is T is atomic, we can't convert `shared Cell[Data]` to `shared Cell[shared Data]`.
    crate::assert_err!({
        struct Data {}
        struct Cell[ty T]
        where
            T is atomic,
        {
            atomic f: T;
        }
        struct Main {
            fn test(^ self, d1: shared Cell[Data]) -> shared Cell[shared Data] {
                d1^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Cell [ty] where ^ty0_0 is atomic { atomic f : ^ty0_0 ; } struct Main { fn test (^ self d1 : shared Cell[Data]) -> shared Cell[shared Data] { d1 ^ ; } } }`"]);
}

#[test]
#[allow(non_snake_case)]
fn Cell_rel_T_our_Cell_Data_to_our_Cell_our_Data() {
    // Since T is T is relative, we can't convert `shared Cell[Data]` to `shared Cell[shared Data]`.
    crate::assert_err!({
        struct Data {}
        struct Cell[ty T]
        where
            T is relative,
        {
        }
        struct Main {
            fn test(^ self, d1: shared Cell[Data]) -> shared Cell[shared Data] {
                d1^;
            }
        }
        }, expect_test::expect!["judgment had no applicable rules: `check_program { program: struct Data { } struct Cell [ty] where ^ty0_0 is relative { } struct Main { fn test (^ self d1 : shared Cell[Data]) -> shared Cell[shared Data] { d1 ^ ; } } }`"]);
}

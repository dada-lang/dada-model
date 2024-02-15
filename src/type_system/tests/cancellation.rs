use crate::{dada_lang::term, type_system::check_program};
use formality_core::{test, test_util::ResultTestExt};

#[test]
#[allow(non_snake_case)]
#[ignore = "FIXME: cancellation not implemented"]
fn our_leased_to_our() {
    check_program(&term(
        "
        class Data {
            fn read[perm P](P self) where shared(P) {
                ();
            }
        }
        class Main {
            fn test(my self) {
                let d = new Data();
                let p: leased{d} Data = d.lease;
                let q: shared{p} Data = p.share;
                let r: our leased{d} Data = q.give;
                r.give.read();
            }
        }
        ",
    ))
    .assert_ok(expect_test::expect![["()"]]);
}

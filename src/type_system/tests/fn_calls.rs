use formality_core::test;

/// Check giving different messages in two fn calls works.
#[test]
#[allow(non_snake_case)]
fn send_two_different_messages() {
    crate::assert_ok!({
            class Bar {}

            class Channel[ty M] {
                fn send[perm P](P self, msg: M)
                where
                  mut(P),
                {
                }
            }

            class TheClass {
                fn empty_method(given self) {
                    let channel = new Channel[Bar]();

                    let bar1 = new Bar();
                    channel.mut.send[mut[channel]](bar1.give);

                    let bar2 = new Bar();
                    channel.mut.send[mut[channel]](bar2.give);

                    ();
                }
            }
        })
}

/// Check that giving same message twice in fn calls errors.
#[test]
#[allow(non_snake_case)]
fn send_same_message_twice() {
    crate::assert_err!({
            class Bar {}

            class Channel[ty M] {
                fn send[perm P](P self, msg: M)
                where
                    mut(P),
                {
                }
            }

            class TheClass {
                fn empty_method(given self) {
                    let channel = new Channel[Bar]();
                    let bar = new Bar();
                    channel.mut.send[mut[channel]](bar.give);
                    channel.mut.send[mut[channel]](bar.give);
                    ();
                }
            }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn empty_method (given self) -> () { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . mut . send [mut [channel]] (bar . give) ; channel . mut . send [mut [channel]] (bar . give) ; () ; }, class_ty: TheClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . mut . send [mut [channel]] (bar . give) ; channel . mut . send [mut [channel]] (bar . give) ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . mut . send [mut [channel]] (bar . give) ; channel . mut . send [mut [channel]] (bar . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . mut . send [mut [channel]] (bar . give) ; channel . mut . send [mut [channel]] (bar . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . mut . send [mut [channel]] (bar . give) ; channel . mut . send [mut [channel]] (bar . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . mut . send [mut [channel]] (bar . give) ; channel . mut . send [mut [channel]] (bar . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let channel = new Channel [Bar] () ;, let bar = new Bar () ;, channel . mut . send [mut [channel]] (bar . give) ;, channel . mut . send [mut [channel]] (bar . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let bar = new Bar () ;, channel . mut . send [mut [channel]] (bar . give) ;, channel . mut . send [mut [channel]] (bar . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [channel . mut . send [mut [channel]] (bar . give) ;, channel . mut . send [mut [channel]] (bar . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statement { statement: channel . mut . send [mut [channel]] (bar . give) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar, channel}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "expr" at (statements.rs) failed because
                                                      judgment `type_expr { expr: channel . mut . send [mut [channel]] (bar . give), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {bar, channel}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "call" at (expressions.rs) failed because
                                                          judgment `type_method_arguments_as { exprs: [bar . give], input_temps: [@ fresh(0)], input_names: [msg], input_tys: [Bar], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): mut [channel] Channel[Bar], bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {bar, channel}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "cons" at (expressions.rs) failed because
                                                              judgment `type_expr { expr: bar . give, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): mut [channel] Channel[Bar], bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {@ fresh(0), bar, channel}, traversed: {} } }` failed at the following rule(s):
                                                                the rule "give place" at (expressions.rs) failed because
                                                                  judgment `move_place { place: bar, ty: Bar, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): mut [channel] Channel[Bar], bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {@ fresh(0), bar, channel}, traversed: {} } }` failed at the following rule(s):
                                                                    the rule "copy" at (expressions.rs) failed because
                                                                      judgment `prove_is_copy { a: Bar, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): mut [channel] Channel[Bar], bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                        the rule "is" at (predicates.rs) failed because
                                                                          judgment `prove_predicate { predicate: copy(Bar), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): mut [channel] Channel[Bar], bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 1 } }` failed at the following rule(s):
                                                                            the rule "parameter" at (predicates.rs) failed because
                                                                              pattern `true` did not match value `false`
                                                                    the rule "give" at (expressions.rs) failed because
                                                                      condition evaluted to false: `!live_after.is_live(&place)`
                                                                        live_after = LivePlaces { accessed: {@ fresh(0), bar, channel}, traversed: {} }
                                                                        &place = bar"#]])
}

/// Check that calling channel with a copy(self) when mut(self) is declared errors.
#[test]
#[allow(non_snake_case)]
fn needs_leased_got_shared_self() {
    crate::assert_err!({
            class Bar {}

            class Channel[ty M] {
                fn send[perm P](P self, msg: M)
                where
                    mut(P),
                {
                }
            }

            class TheClass {
                fn empty_method(given self) {
                    let channel = new Channel[Bar]();
                    let bar = new Bar();
                    channel.ref.send[ref[channel]](bar.give);
                    ();
                }
            }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn empty_method (given self) -> () { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . ref . send [ref [channel]] (bar . give) ; () ; }, class_ty: TheClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . ref . send [ref [channel]] (bar . give) ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . ref . send [ref [channel]] (bar . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . ref . send [ref [channel]] (bar . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . ref . send [ref [channel]] (bar . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let channel = new Channel [Bar] () ; let bar = new Bar () ; channel . ref . send [ref [channel]] (bar . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let channel = new Channel [Bar] () ;, let bar = new Bar () ;, channel . ref . send [ref [channel]] (bar . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let bar = new Bar () ;, channel . ref . send [ref [channel]] (bar . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [channel . ref . send [ref [channel]] (bar . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statement { statement: channel . ref . send [ref [channel]] (bar . give) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "expr" at (statements.rs) failed because
                                                      judgment `type_expr { expr: channel . ref . send [ref [channel]] (bar . give), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "call" at (expressions.rs) failed because
                                                          judgment `prove_predicates { predicate: [mut(ref [channel])], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): ref [channel] Channel[Bar], @ fresh(1): Bar, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                            the rule "prove_predicates" at (predicates.rs) failed because
                                                              judgment `prove_predicate { predicate: mut(ref [channel]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): ref [channel] Channel[Bar], @ fresh(1): Bar, bar: Bar, channel: Channel[Bar]}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                                the rule "parameter" at (predicates.rs) failed because
                                                                  pattern `true` did not match value `false`"#]])
}

/// Test where function expects a `Pair` and data borrowed from `pair`.
/// We `give` data shared from `pair.a`.
/// OK.
#[test]
#[allow(non_snake_case)]
fn take_pair_and_data__give_pair_give_data_ok() {
    crate::assert_ok!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;
            }

            class TheClass {
                fn take_pair_and_data[perm P](P self, pair: given Pair, data: ref[pair] Data) {

                }

                fn empty_method(given self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.ref;
                    self.give.take_pair_and_data[given](pair.give, data.give);
                    ();
                }
            }
        })
}

/// Test where function expects a `Pair` and data borrowed from `pair`.
/// We `share` data shared from `pair.a`.
/// OK.
#[test]
#[allow(non_snake_case)]
fn take_pair_and_data__give_pair_share_data_ok() {
    crate::assert_ok!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;
            }

            class TheClass {
                fn take_pair_and_data[perm P](P self, pair: given Pair, data: ref[pair] Data) {

                }

                fn empty_method(given self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.ref;
                    self.give.take_pair_and_data[given](pair.give, data.ref);
                    ();
                }
            }
        })
}

/// Test where function expects a `Pair` and data borrowed from `pair`.
/// We `share` data shared from `pair.a` but use it later.
/// Should error because `pair` has been moved.
#[test]
#[allow(non_snake_case)]
fn take_pair_and_data__give_pair_share_data_share_later() {
    crate::assert_err!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;
            }

            class TheClass {
                fn take_pair_and_data[perm P](P self, pair: given Pair, data: ref[pair] Data) {

                }

                fn empty_method(given self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.ref;
                    self.give.take_pair_and_data[given](pair.give, data.ref);
                    data.ref;
                    ();
                }
            }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn empty_method (given self) -> () { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . give . take_pair_and_data [given] (pair . give, data . ref) ; data . ref ; () ; }, class_ty: TheClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . give . take_pair_and_data [given] (pair . give, data . ref) ; data . ref ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . give . take_pair_and_data [given] (pair . give, data . ref) ; data . ref ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . give . take_pair_and_data [given] (pair . give, data . ref) ; data . ref ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . give . take_pair_and_data [given] (pair . give, data . ref) ; data . ref ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . give . take_pair_and_data [given] (pair . give, data . ref) ; data . ref ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let pair = new Pair (new Data (), new Data ()) ;, let data = pair . a . ref ;, self . give . take_pair_and_data [given] (pair . give, data . ref) ;, data . ref ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let data = pair . a . ref ;, self . give . take_pair_and_data [given] (pair . give, data . ref) ;, data . ref ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [self . give . take_pair_and_data [given] (pair . give, data . ref) ;, data . ref ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, data: ref [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statement { statement: self . give . take_pair_and_data [given] (pair . give, data . ref) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, data: ref [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "expr" at (statements.rs) failed because
                                                      judgment `type_expr { expr: self . give . take_pair_and_data [given] (pair . give, data . ref), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, data: ref [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "call" at (expressions.rs) failed because
                                                          judgment `accesses_permitted { access: drop, places: [@ fresh(2), @ fresh(1), @ fresh(0)], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): given TheClass, @ fresh(1): Pair, @ fresh(2): ref [data] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "accesses_permitted" at (accesses.rs) failed because
                                                              judgment `"flat_map"` failed at the following rule(s):
                                                                failed at (quantifiers.rs) because
                                                                  judgment `access_permitted { access: drop, place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): given TheClass, @ fresh(1): Pair, @ fresh(2): ref [data] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                                    the rule "access_permitted" at (accesses.rs) failed because
                                                                      judgment `env_permits_access { access: drop, place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): given TheClass, @ fresh(1): Pair, @ fresh(2): ref [data] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                                        the rule "env_permits_access" at (accesses.rs) failed because
                                                                          judgment `parameters_permit_access { parameters: [ref [@ fresh(1) . a] Data], access: drop, place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): given TheClass, @ fresh(1): Pair, @ fresh(2): ref [data] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                            the rule "cons" at (accesses.rs) failed because
                                                                              judgment `parameter_permits_access { parameter: ref [@ fresh(1) . a] Data, access: drop, place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): given TheClass, @ fresh(1): Pair, @ fresh(2): ref [data] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                                the rule "parameter" at (accesses.rs) failed because
                                                                                  judgment `lien_permit_access { lien: rf(@ fresh(1) . a), access: drop, accessed_place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): given TheClass, @ fresh(1): Pair, @ fresh(2): ref [data] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                                    the rule "ref'd" at (accesses.rs) failed because
                                                                                      judgment `ref_place_permits_access { shared_place: @ fresh(1) . a, access: drop, accessed_place: @ fresh(1) }` failed at the following rule(s):
                                                                                        the rule "share-mutation" at (accesses.rs) failed because
                                                                                          condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                                            &accessed_place = @ fresh(1)
                                                                                            &shared_place = @ fresh(1) . a"#]])
}

/// Test where function expects a `Pair` and data borrowed from `pair`.
/// We `give` data shared from `pair.a` but use it later.
/// Should error because `pair` has been moved.
#[test]
#[allow(non_snake_case)]
fn take_pair_and_data__give_pair_give_data_give_later() {
    crate::assert_err!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;
            }

            class TheClass {
                fn take_pair_and_data[perm P](P self, pair: given Pair, data: ref[pair] Data) {

                }

                fn empty_method(given self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.ref;
                    self.give.take_pair_and_data[given](pair.give, data.give);
                    data.give;
                    ();
                }
            }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn empty_method (given self) -> () { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . give . take_pair_and_data [given] (pair . give, data . give) ; data . give ; () ; }, class_ty: TheClass, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . give . take_pair_and_data [given] (pair . give, data . give) ; data . give ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . give . take_pair_and_data [given] (pair . give, data . give) ; data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . give . take_pair_and_data [given] (pair . give, data . give) ; data . give ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . give . take_pair_and_data [given] (pair . give, data . give) ; data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . a . ref ; self . give . take_pair_and_data [given] (pair . give, data . give) ; data . give ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let pair = new Pair (new Data (), new Data ()) ;, let data = pair . a . ref ;, self . give . take_pair_and_data [given] (pair . give, data . give) ;, data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let data = pair . a . ref ;, self . give . take_pair_and_data [given] (pair . give, data . give) ;, data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [self . give . take_pair_and_data [given] (pair . give, data . give) ;, data . give ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, data: ref [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statement { statement: self . give . take_pair_and_data [given] (pair . give, data . give) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, data: ref [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "expr" at (statements.rs) failed because
                                                      judgment `type_expr { expr: self . give . take_pair_and_data [given] (pair . give, data . give), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, data: ref [pair . a] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "call" at (expressions.rs) failed because
                                                          judgment `accesses_permitted { access: drop, places: [@ fresh(2), @ fresh(1), @ fresh(0)], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): given TheClass, @ fresh(1): Pair, @ fresh(2): ref [@ fresh(1) . a] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "accesses_permitted" at (accesses.rs) failed because
                                                              judgment `"flat_map"` failed at the following rule(s):
                                                                failed at (quantifiers.rs) because
                                                                  judgment `access_permitted { access: drop, place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): given TheClass, @ fresh(1): Pair, @ fresh(2): ref [@ fresh(1) . a] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                                    the rule "access_permitted" at (accesses.rs) failed because
                                                                      judgment `env_permits_access { access: drop, place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): given TheClass, @ fresh(1): Pair, @ fresh(2): ref [@ fresh(1) . a] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 }, live_after: LivePlaces { accessed: {data}, traversed: {} } }` failed at the following rule(s):
                                                                        the rule "env_permits_access" at (accesses.rs) failed because
                                                                          judgment `parameters_permit_access { parameters: [ref [@ fresh(1) . a] Data], access: drop, place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): given TheClass, @ fresh(1): Pair, @ fresh(2): ref [@ fresh(1) . a] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                            the rule "cons" at (accesses.rs) failed because
                                                                              judgment `parameter_permits_access { parameter: ref [@ fresh(1) . a] Data, access: drop, place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): given TheClass, @ fresh(1): Pair, @ fresh(2): ref [@ fresh(1) . a] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                                the rule "parameter" at (accesses.rs) failed because
                                                                                  judgment `lien_permit_access { lien: rf(@ fresh(1) . a), access: drop, accessed_place: @ fresh(1), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given TheClass, @ fresh(0): given TheClass, @ fresh(1): Pair, @ fresh(2): ref [@ fresh(1) . a] Data, data: ref [@ fresh(1) . a] Data, pair: Pair}, assumptions: {}, fresh: 3 } }` failed at the following rule(s):
                                                                                    the rule "ref'd" at (accesses.rs) failed because
                                                                                      judgment `ref_place_permits_access { shared_place: @ fresh(1) . a, access: drop, accessed_place: @ fresh(1) }` failed at the following rule(s):
                                                                                        the rule "share-mutation" at (accesses.rs) failed because
                                                                                          condition evaluted to false: `place_disjoint_from(&accessed_place, &shared_place)`
                                                                                            &accessed_place = @ fresh(1)
                                                                                            &shared_place = @ fresh(1) . a"#]])
}

/// Test where we expect data leased from self (but do nothing with it).
/// OK.
#[test]
#[allow(non_snake_case)]
fn pair_method__leased_self_ok() {
    crate::assert_ok!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, data: mut[self] Data) {
                  ();
                }
            }

            class Main {
                fn main(given self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.mut;
                    pair.give.method(data.give);
                    ();
                }
            }
        })
}

/// Test where we expect data ref'd from self (but do nothing with it).
/// OK.
#[test]
#[allow(non_snake_case)]
fn pair_method__ref_self_ok() {
    crate::assert_ok!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, data: ref[self] Data) {
                  ();
                }
            }

            class Main {
                fn main(given self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.a.ref;
                    pair.give.method(data.give);
                    ();
                }
            }
        })
}

/// Test where we expect data leased from self.a but get data from self.b.
/// Error.
#[test]
#[allow(non_snake_case)]
fn pair_method__expect_leased_self_a__got_leased_self_b() {
    crate::assert_err!({
            class Data {}

            class Pair {
                a: Data;
                b: Data;

                fn method(given self, data: mut[self.a] Data) {
                  ();
                }
            }

            class Main {
                fn main(given self) {
                    let pair = new Pair(new Data(), new Data());
                    let data = pair.b.mut;
                    pair.give.method(data.give);
                    ();
                }
            }
        }, expect_test::expect![[r#"
            the rule "check_class" at (classes.rs) failed because
              judgment `check_method { decl: fn main (given self) -> () { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . mut ; pair . give . method (data . give) ; () ; }, class_ty: Main, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                the rule "check_method" at (methods.rs) failed because
                  judgment `check_body { body: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . mut ; pair . give . method (data . give) ; () ; }, output: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 } }` failed at the following rule(s):
                    the rule "block" at (methods.rs) failed because
                      judgment `can_type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . mut ; pair . give . method (data . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                        the rule "can_type_expr_as" at (expressions.rs) failed because
                          judgment `type_expr_as { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . mut ; pair . give . method (data . give) ; () ; }, as_ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                            the rule "type_expr_as" at (expressions.rs) failed because
                              judgment `type_expr { expr: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . mut ; pair . give . method (data . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                the rule "block" at (expressions.rs) failed because
                                  judgment `type_block { block: { let pair = new Pair (new Data (), new Data ()) ; let data = pair . b . mut ; pair . give . method (data . give) ; () ; }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                    the rule "place" at (blocks.rs) failed because
                                      judgment `type_statements_with_final_ty { statements: [let pair = new Pair (new Data (), new Data ()) ;, let data = pair . b . mut ;, pair . give . method (data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                        the rule "cons" at (statements.rs) failed because
                                          judgment `type_statements_with_final_ty { statements: [let data = pair . b . mut ;, pair . give . method (data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                            the rule "cons" at (statements.rs) failed because
                                              judgment `type_statements_with_final_ty { statements: [pair . give . method (data . give) ;, () ;], ty: (), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [pair . b] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                the rule "cons" at (statements.rs) failed because
                                                  judgment `type_statement { statement: pair . give . method (data . give) ;, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [pair . b] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                    the rule "expr" at (statements.rs) failed because
                                                      judgment `type_expr { expr: pair . give . method (data . give), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, data: mut [pair . b] Data, pair: Pair}, assumptions: {}, fresh: 0 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                        the rule "call" at (expressions.rs) failed because
                                                          judgment `type_method_arguments_as { exprs: [data . give], input_temps: [@ fresh(0)], input_names: [data], input_tys: [mut [@ fresh(0) . a] Data], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Pair, data: mut [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 1 }, live_after: LivePlaces { accessed: {}, traversed: {} } }` failed at the following rule(s):
                                                            the rule "cons" at (expressions.rs) failed because
                                                              judgment `sub { a: mut [@ fresh(0) . b] Data, b: mut [@ fresh(0) . a] Data, live_after: LivePlaces { accessed: {@ fresh(0)}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Pair, @ fresh(1): mut [@ fresh(0) . b] Data, data: mut [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                                the rule "sub-classes" at (subtypes.rs) failed because
                                                                  judgment `sub_perms { perm_a: mut [@ fresh(0) . b], perm_b: mut [@ fresh(0) . a], live_after: LivePlaces { accessed: {@ fresh(0)}, traversed: {} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Pair, @ fresh(1): mut [@ fresh(0) . b] Data, data: mut [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                                    the rule "sub_red_perms" at (redperms.rs) failed because
                                                                      judgment `red_chain_sub_perm { red_chain_a: RedChain { links: [Mtl(@ fresh(0) . b)] }, red_perm_b: RedPerm { chains: {RedChain { links: [Mtl(@ fresh(0) . a)] }} }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Pair, @ fresh(1): mut [@ fresh(0) . b] Data, data: mut [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                                        the rule "sub_red_perms" at (redperms.rs) failed because
                                                                          judgment `red_chain_sub_chain { red_chain_a: RedChain { links: [Mtl(@ fresh(0) . b)] }, red_chain_b: RedChain { links: [Mtl(@ fresh(0) . a)] }, env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Pair, @ fresh(1): mut [@ fresh(0) . b] Data, data: mut [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                                            the rule "(mut::P) vs (mut::P)" at (redperms.rs) failed because
                                                                              condition evaluted to false: `place_b.is_prefix_of(&place_a)`
                                                                                place_b = @ fresh(0) . a
                                                                                &place_a = @ fresh(0) . b
                                                                            the rule "(shared::P) vs (copy::P)" at (redperms.rs) failed because
                                                                              judgment `prove_is_copy_owned { a: mut [@ fresh(0) . b], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Pair, @ fresh(1): mut [@ fresh(0) . b] Data, data: mut [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                                                the rule "prove" at (predicates.rs) failed because
                                                                                  judgment `prove_is_copy { a: mut [@ fresh(0) . b], env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Pair, @ fresh(1): mut [@ fresh(0) . b] Data, data: mut [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                                                    the rule "is" at (predicates.rs) failed because
                                                                                      judgment `prove_predicate { predicate: copy(mut [@ fresh(0) . b]), env: Env { program: "...", universe: universe(0), in_scope_vars: [], local_variables: {self: given Main, @ fresh(0): Pair, @ fresh(1): mut [@ fresh(0) . b] Data, data: mut [@ fresh(0) . b] Data, pair: Pair}, assumptions: {}, fresh: 2 } }` failed at the following rule(s):
                                                                                        the rule "parameter" at (predicates.rs) failed because
                                                                                          pattern `true` did not match value `false`"#]])
}

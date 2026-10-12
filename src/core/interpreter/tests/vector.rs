/// Tests for Vec and Iterator — the capstone integration tests (Phase 5).
///
/// These tests exercise the full stack: classes with drop bodies, is_last_ref,
/// array intrinsics with poly-permission dispatch, and whole-place drop semantics.
///
/// Most tests use `vec_test!` which injects the standard Vec and Iterator
/// definitions and runs an interpreter-only test (the type checker doesn't yet
/// fully support the permission patterns Vec uses).

/// Returns the standard Vec and Iterator class definitions from the design doc.
///
/// Design note on Iterator.drop: no `is_last_ref` guard is needed (unlike Vec.drop)
/// because the poly-permission `P` already handles all cases correctly:
///   - P=given:  `array_drop` drops remaining elements (we own them)
///   - P=shared: `array_drop` is a no-op (we don't own them)
///   - P=place sharing:    `array_drop` is a no-op (we don't own them)
/// Vec.drop needs `is_last_ref` because it runs on *every* handle drop (shared
/// handles each trigger the drop body), but Iterator.drop's `array_drop[T, P, ...]`
/// naturally dispatches on the permission the iterator was created with.
fn vec_prelude() -> &'static str {
    r#"
    struct Vec[type T] {
        data: Array[T];
        len: Int;

        fn push[perm P](P self, value: given T) → ()
        where
            P is mut,
        {
            array_write[T, ![self.data]](self.data!, self.len→, value→);
            self.len = self.len→ + 1;
            ();
        }

        fn get[perm P](P self, index: given Int) → given[self] T {
            let data: given[self.data] Array[T] = self.data→;
            let len: Int = self.len→;
            array_drop[T, given[self], shared[data]](data.share, 0, index→);
            array_drop[T, given[self], shared[data]](data.share, index→ + 1, len→);
            array_give[T, given[self], shared[data]](data.share, index→);
        }

        fn iter[perm P](P self) → Iterator[P, T] {
            new Iterator[P, T](self→, 0);
        }

        drop {
            if is_last_ref[shared[self.data]](self.data.share) {
                array_drop[T, given, shared[self.data]](self.data.share, 0, self.len→);
            } else {
                ();
            };
        }
    }

    struct Iterator[perm P, type T] {
        vec: P Vec[T];
        start: Int;

        fn next[perm I](I self) → P T
        where
            I is mut,
        {
            let index: Int = self.start→;
            self.start = self.start→ + 1;
            array_give[T, P, shared[self.vec.data]](self.vec.data.share, index→);
        }

        drop {
            let data: given[self.vec.data] Array[T] = self.vec.data→;
            let start: Int = self.start→;
            let len: Int = self.vec.len→;
            array_drop[T, P, shared[data]](data.share, start→, len→);
        }
    }
    "#
}

/// Runs an interpreter-only test with the Vec prelude prepended.
macro_rules! vec_test {
    ({ $($extra:tt)* }, $expect:expr) => {{
        vec_test!(stringify!($($extra)*), $expect);
    }};

    ($extra:expr, $expect:expr) => {{
        let program = format!("{} {}", vec_prelude(), $extra);
        let r = $crate::test_util::test_interpret_only(&program)
            .expect("parse error");
        assert!(
            r.result.starts_with("Ok:"),
            "unexpected interpreter fault:\n{}",
            r.to_snapshot(),
        );
        $expect.assert_eq(&r.to_snapshot());
    }};
}

// ---------------------------------------------------------------
// Vec push basics
// ---------------------------------------------------------------

#[test]
fn vec_push_increments_len() {
    vec_test!(
        r#"
        struct Main {
            fn main(given self) → () {
                let v: given Vec[Int] = new Vec[Int](array_new[Int](4), 0);
                v!push[![v]](42);
                print(v.len→);
                ();
            }
        }
    "#,
        expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_v : given Vec[Int] = new Vec [Int] (array_new [Int](4), 0) ;
        Output: Trace:   _1_v = Vec { data: Array { flag: Given, rc: 1, ⚡, ⚡, ⚡, ⚡ }, len: 0 }
        Output: Trace:   _1_v ! . push [! [_1_v]] (42) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Int, ! [_2_self . data]](_2_self . data ! , _2_self . len → , _2_value →) ;
        Output: Trace:     _2_self . len = _2_self . len → + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   print(_1_v . len →) ;
        Output: ----->   1
        Output: Trace:   () ;
        Output: Trace:   drop Vec
        Output: Trace:     if is_last_ref [shared [self . data]](self . data . share) { array_drop [Int, given, shared [self . data]](self . data . share , 0 , self . len →) ; } else { () ; } ;
        Output: Trace:     array_drop [Int, given, shared [self . data]](self . data . share , 0 , self . len →) ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]
    );
}

// ---------------------------------------------------------------
// Vec push + get with P=given (move semantics)
// ---------------------------------------------------------------

#[test]
fn vec_push_and_get_given() {
    // Push 3 elements, then get(1) with P=given.
    // Drops elements 0 and 2, returns element 1.
    vec_test!(
        r#"
        struct Data {
            value: Int;

            drop {
                print(self.value→);
            }
        }

        struct Main {
            fn main(given self) → () {
                let v: given Vec[Data] = new Vec[Data](array_new[Data](4), 0);
                v!push[![v]](new Data(10));
                v!push[![v]](new Data(20));
                v!push[![v]](new Data(30));
                let got: given Data = v→get[given](1);
                print(got.value→);
                ();
            }
        }
    "#,
        expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_v : given Vec[Data] = new Vec [Data] (array_new [Data](4), 0) ;
        Output: Trace:   _1_v = Vec { data: Array { flag: Given, rc: 1, Data { value: ⚡ }, Data { value: ⚡ }, Data { value: ⚡ }, Data { value: ⚡ } }, len: 0 }
        Output: Trace:   _1_v ! . push [! [_1_v]] (new Data (10)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Data, ! [_2_self . data]](_2_self . data ! , _2_self . len → , _2_value →) ;
        Output: Trace:     _2_self . len = _2_self . len → + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_v ! . push [! [_1_v]] (new Data (20)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Data, ! [_3_self . data]](_3_self . data ! , _3_self . len → , _3_value →) ;
        Output: Trace:     _3_self . len = _3_self . len → + 1 ;
        Output: Trace:     _3_self . len = 2
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_v ! . push [! [_1_v]] (new Data (30)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Data, ! [_4_self . data]](_4_self . data ! , _4_self . len → , _4_value →) ;
        Output: Trace:     _4_self . len = _4_self . len → + 1 ;
        Output: Trace:     _4_self . len = 3
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_got : given Data = _1_v → . get [given] (1) ;
        Output: Trace:   enter Vec.get
        Output: Trace:     let _5_data : given [_5_self . data] Array[Data] = _5_self . data → ;
        Output: Trace:     _5_data = Array { flag: Given, rc: 1, Data { value: 10 }, Data { value: 20 }, Data { value: 30 }, Data { value: ⚡ } }
        Output: Trace:     let _5_len : Int = _5_self . len → ;
        Output: Trace:     _5_len = 3
        Output: Trace:     array_drop [Data, given [_5_self], shared [_5_data]](_5_data . share , 0 , _5_index →) ;
        Output: Trace:     drop Data
        Output: Trace:       print(self . value →) ;
        Output: ----->       10
        Output: Trace:     array_drop [Data, given [_5_self], shared [_5_data]](_5_data . share , _5_index → + 1 , _5_len →) ;
        Output: Trace:     drop Data
        Output: Trace:       print(self . value →) ;
        Output: ----->       30
        Output: Trace:     array_give [Data, given [_5_self], shared [_5_data]](_5_data . share , _5_index →) ;
        Output: Trace:   exit Vec.get => Data { value: 20 }
        Output: Trace:   _1_got = Data { value: 20 }
        Output: Trace:   print(_1_got . value →) ;
        Output: ----->   20
        Output: Trace:   () ;
        Output: Trace:   drop Data
        Output: Trace:     print(self . value →) ;
        Output: ----->     20
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]
    );
}

// ---------------------------------------------------------------
// Vec drop cleans all elements
// ---------------------------------------------------------------

#[test]
fn vec_drop_cleans_all_elements() {
    vec_test!(
        r#"
        struct Item {
            val: Int;

            drop {
                print(self.val→);
            }
        }

        struct Main {
            fn main(given self) → () {
                let v: given Vec[Item] = new Vec[Item](array_new[Item](4), 0);
                v!push[![v]](new Item(100));
                v!push[![v]](new Item(200));
                v!push[![v]](new Item(300));
                ();
            }
        }
    "#,
        expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_v : given Vec[Item] = new Vec [Item] (array_new [Item](4), 0) ;
        Output: Trace:   _1_v = Vec { data: Array { flag: Given, rc: 1, Item { val: ⚡ }, Item { val: ⚡ }, Item { val: ⚡ }, Item { val: ⚡ } }, len: 0 }
        Output: Trace:   _1_v ! . push [! [_1_v]] (new Item (100)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Item, ! [_2_self . data]](_2_self . data ! , _2_self . len → , _2_value →) ;
        Output: Trace:     _2_self . len = _2_self . len → + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_v ! . push [! [_1_v]] (new Item (200)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Item, ! [_3_self . data]](_3_self . data ! , _3_self . len → , _3_value →) ;
        Output: Trace:     _3_self . len = _3_self . len → + 1 ;
        Output: Trace:     _3_self . len = 2
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_v ! . push [! [_1_v]] (new Item (300)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Item, ! [_4_self . data]](_4_self . data ! , _4_self . len → , _4_value →) ;
        Output: Trace:     _4_self . len = _4_self . len → + 1 ;
        Output: Trace:     _4_self . len = 3
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   () ;
        Output: Trace:   drop Vec
        Output: Trace:     if is_last_ref [shared [self . data]](self . data . share) { array_drop [Item, given, shared [self . data]](self . data . share , 0 , self . len →) ; } else { () ; } ;
        Output: Trace:     array_drop [Item, given, shared [self . data]](self . data . share , 0 , self . len →) ;
        Output: Trace:     drop Item
        Output: Trace:       print(self . val →) ;
        Output: ----->       100
        Output: Trace:     drop Item
        Output: Trace:       print(self . val →) ;
        Output: ----->       200
        Output: Trace:     drop Item
        Output: Trace:       print(self . val →) ;
        Output: ----->       300
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]
    );
}

// ---------------------------------------------------------------
// Vec iter and next (given permission, consuming)
// ---------------------------------------------------------------

#[test]
fn vec_iter_and_next() {
    // Consuming iterator: next() moves element 0, drop cleans 1 and 2.
    vec_test!(
        r#"
        struct Item {
            val: Int;

            drop {
                print(self.val→);
            }
        }

        struct Main {
            fn main(given self) → () {
                let v: given Vec[Item] = new Vec[Item](array_new[Item](4), 0);
                v!push[![v]](new Item(10));
                v!push[![v]](new Item(20));
                v!push[![v]](new Item(30));
                let it: Iterator[given, Item] = v→iter[given]();
                let first: given Item = it!next[![it]]();
                print(first.val→);
                ();
            }
        }
    "#,
        expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_v : given Vec[Item] = new Vec [Item] (array_new [Item](4), 0) ;
        Output: Trace:   _1_v = Vec { data: Array { flag: Given, rc: 1, Item { val: ⚡ }, Item { val: ⚡ }, Item { val: ⚡ }, Item { val: ⚡ } }, len: 0 }
        Output: Trace:   _1_v ! . push [! [_1_v]] (new Item (10)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Item, ! [_2_self . data]](_2_self . data ! , _2_self . len → , _2_value →) ;
        Output: Trace:     _2_self . len = _2_self . len → + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_v ! . push [! [_1_v]] (new Item (20)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Item, ! [_3_self . data]](_3_self . data ! , _3_self . len → , _3_value →) ;
        Output: Trace:     _3_self . len = _3_self . len → + 1 ;
        Output: Trace:     _3_self . len = 2
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_v ! . push [! [_1_v]] (new Item (30)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Item, ! [_4_self . data]](_4_self . data ! , _4_self . len → , _4_value →) ;
        Output: Trace:     _4_self . len = _4_self . len → + 1 ;
        Output: Trace:     _4_self . len = 3
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_it : Iterator[given, Item] = _1_v → . iter [given] () ;
        Output: Trace:   enter Vec.iter
        Output: Trace:     new Iterator [given, Item] (_5_self →, 0) ;
        Output: Trace:   exit Vec.iter => Iterator { vec: Vec { data: Array { flag: Given, rc: 1, Item { val: 10 }, Item { val: 20 }, Item { val: 30 }, Item { val: ⚡ } }, len: 3 }, start: 0 }
        Output: Trace:   _1_it = Iterator { vec: Vec { data: Array { flag: Given, rc: 1, Item { val: 10 }, Item { val: 20 }, Item { val: 30 }, Item { val: ⚡ } }, len: 3 }, start: 0 }
        Output: Trace:   let _1_first : given Item = _1_it ! . next [! [_1_it]] () ;
        Output: Trace:   enter Iterator.next
        Output: Trace:     let _6_index : Int = _6_self . start → ;
        Output: Trace:     _6_index = 0
        Output: Trace:     _6_self . start = _6_self . start → + 1 ;
        Output: Trace:     _6_self . start = 1
        Output: Trace:     array_give [Item, given, shared [_6_self . vec . data]](_6_self . vec . data . share , _6_index →) ;
        Output: Trace:   exit Iterator.next => Item { val: 10 }
        Output: Trace:   _1_first = Item { val: 10 }
        Output: Trace:   print(_1_first . val →) ;
        Output: ----->   10
        Output: Trace:   () ;
        Output: Trace:   drop Item
        Output: Trace:     print(self . val →) ;
        Output: ----->     10
        Output: Trace:   drop Iterator
        Output: Trace:     let data : given [self . vec . data] Array[Item] = self . vec . data → ;
        Output: Trace:     data = shared [@ magic] Array { flag: SharedPlace, rc: 1, Item { val: ⚡ }, Item { val: 20 }, Item { val: 30 }, Item { val: ⚡ } }
        Output: Trace:     let start : Int = self . start → ;
        Output: Trace:     start = 1
        Output: Trace:     let len : Int = self . vec . len → ;
        Output: Trace:     len = 3
        Output: Trace:     array_drop [Item, given, shared [data]](data . share , start → , len →) ;
        Output: Trace:     drop Item
        Output: Trace:       print(self . val →) ;
        Output: ----->       20
        Output: Trace:     drop Item
        Output: Trace:       print(self . val →) ;
        Output: ----->       30
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]
    );
}

// ---------------------------------------------------------------
// Shared Vec get (P=shared, non-consuming)
// ---------------------------------------------------------------

#[test]
fn shared_vec_get() {
    // P=shared: array_drop is no-op, array_give copies.
    vec_test!(
        r#"
        struct Data {
            value: Int;
        }

        struct Main {
            fn main(given self) → () {
                let v: given Vec[Data] = new Vec[Data](array_new[Data](4), 0);
                v!push[![v]](new Data(10));
                v!push[![v]](new Data(20));
                let sv: shared Vec[Data] = v→.share;
                let got: shared Data = sv→get[shared](0);
                print(got→);
                ();
            }
        }
    "#,
        expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_v : given Vec[Data] = new Vec [Data] (array_new [Data](4), 0) ;
        Output: Trace:   _1_v = Vec { data: Array { flag: Given, rc: 1, Data { value: ⚡ }, Data { value: ⚡ }, Data { value: ⚡ }, Data { value: ⚡ } }, len: 0 }
        Output: Trace:   _1_v ! . push [! [_1_v]] (new Data (10)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Data, ! [_2_self . data]](_2_self . data ! , _2_self . len → , _2_value →) ;
        Output: Trace:     _2_self . len = _2_self . len → + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_v ! . push [! [_1_v]] (new Data (20)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Data, ! [_3_self . data]](_3_self . data ! , _3_self . len → , _3_value →) ;
        Output: Trace:     _3_self . len = _3_self . len → + 1 ;
        Output: Trace:     _3_self . len = 2
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_sv : shared Vec[Data] = _1_v → . share ;
        Output: Trace:   _1_sv = shared Vec { data: Array { flag: SharedOwned, rc: 1, Data { value: 10 }, Data { value: 20 }, Data { value: ⚡ }, Data { value: ⚡ } }, len: 2 }
        Output: Trace:   let _1_got : shared Data = _1_sv → . get [shared] (0) ;
        Output: Trace:   enter Vec.get
        Output: Trace:     let _4_data : given [_4_self . data] Array[Data] = _4_self . data → ;
        Output: Trace:     _4_data = shared Array { flag: SharedOwned, rc: 3, Data { value: 10 }, Data { value: 20 }, Data { value: ⚡ }, Data { value: ⚡ } }
        Output: Trace:     let _4_len : Int = _4_self . len → ;
        Output: Trace:     _4_len = 2
        Output: Trace:     array_drop [Data, given [_4_self], shared [_4_data]](_4_data . share , 0 , _4_index →) ;
        Output: Trace:     array_drop [Data, given [_4_self], shared [_4_data]](_4_data . share , _4_index → + 1 , _4_len →) ;
        Output: Trace:     array_give [Data, given [_4_self], shared [_4_data]](_4_data . share , _4_index →) ;
        Output: Trace:     drop Vec
        Output: Trace:       if is_last_ref [shared [self . data]](self . data . share) { array_drop [Data, given, shared [self . data]](self . data . share , 0 , self . len →) ; } else { () ; } ;
        Output: Trace:       () ;
        Output: Trace:   exit Vec.get => shared Data { value: 10 }
        Output: Trace:   _1_got = shared Data { value: 10 }
        Output: Trace:   print(_1_got →) ;
        Output: ----->   shared Data { value: 10 }
        Output: Trace:   () ;
        Output: Trace:   drop Vec
        Output: Trace:     if is_last_ref [shared [self . data]](self . data . share) { array_drop [Data, given, shared [self . data]](self . data . share , 0 , self . len →) ; } else { () ; } ;
        Output: Trace:     array_drop [Data, given, shared [self . data]](self . data . share , 0 , self . len →) ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]
    );
}

// ---------------------------------------------------------------
// Sharing a Vec place (P=place sharing)
// ---------------------------------------------------------------

#[test]
fn ref_vec_get() {
    // P=place sharing: elements are borrows, Vec remains intact.
    vec_test!(
        r#"
        struct Data {
            value: Int;
        }

        struct Main {
            fn main(given self) → () {
                let v: given Vec[Data] = new Vec[Data](array_new[Data](4), 0);
                v!push[![v]](new Data(10));
                v!push[![v]](new Data(20));
                let got: shared[v] Data = v.share.get[shared[v]](1);
                print(got.value→);
                ();
            }
        }
    "#,
        expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_v : given Vec[Data] = new Vec [Data] (array_new [Data](4), 0) ;
        Output: Trace:   _1_v = Vec { data: Array { flag: Given, rc: 1, Data { value: ⚡ }, Data { value: ⚡ }, Data { value: ⚡ }, Data { value: ⚡ } }, len: 0 }
        Output: Trace:   _1_v ! . push [! [_1_v]] (new Data (10)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Data, ! [_2_self . data]](_2_self . data ! , _2_self . len → , _2_value →) ;
        Output: Trace:     _2_self . len = _2_self . len → + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_v ! . push [! [_1_v]] (new Data (20)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Data, ! [_3_self . data]](_3_self . data ! , _3_self . len → , _3_value →) ;
        Output: Trace:     _3_self . len = _3_self . len → + 1 ;
        Output: Trace:     _3_self . len = 2
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_got : shared [_1_v] Data = _1_v . share . get [shared [_1_v]] (1) ;
        Output: Trace:   enter Vec.get
        Output: Trace:     let _4_data : given [_4_self . data] Array[Data] = _4_self . data → ;
        Output: Trace:     _4_data = shared [_1_v] Array { flag: SharedPlace, rc: 1, Data { value: 10 }, Data { value: 20 }, Data { value: ⚡ }, Data { value: ⚡ } }
        Output: Trace:     let _4_len : Int = _4_self . len → ;
        Output: Trace:     _4_len = 2
        Output: Trace:     array_drop [Data, given [_4_self], shared [_4_data]](_4_data . share , 0 , _4_index →) ;
        Output: Trace:     array_drop [Data, given [_4_self], shared [_4_data]](_4_data . share , _4_index → + 1 , _4_len →) ;
        Output: Trace:     array_give [Data, given [_4_self], shared [_4_data]](_4_data . share , _4_index →) ;
        Output: Trace:   exit Vec.get => shared [_1_v] Data { value: 20 }
        Output: Trace:   _1_got = shared [_1_v] Data { value: 20 }
        Output: Trace:   print(_1_got . value →) ;
        Output: ----->   20
        Output: Trace:   () ;
        Output: Trace:   drop Vec
        Output: Trace:     if is_last_ref [shared [self . data]](self . data . share) { array_drop [Data, given, shared [self . data]](self . data . share , 0 , self . len →) ; } else { () ; } ;
        Output: Trace:     array_drop [Data, given, shared [self . data]](self . data . share , 0 , self . len →) ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]
    );
}

// ---------------------------------------------------------------
// Edge case: Vec[Vec[T]] with P=given — no leaks on nested Vecs
// ---------------------------------------------------------------

#[test]
fn nested_vec_get_given_drops_others() {
    // Vec[Vec[Int]]: push 3 inner Vecs, get(1) with P=given.
    // Inner Vecs at 0 and 2 are dropped (their drop bodies run,
    // cleaning their elements). Element 1 is returned.
    vec_test!(
        r#"
        struct Main {
            fn main(given self) → () {
                let inner0: given Vec[Int] = new Vec[Int](array_new[Int](2), 0);
                inner0!push[![inner0]](100);

                let inner1: given Vec[Int] = new Vec[Int](array_new[Int](2), 0);
                inner1!push[![inner1]](200);

                let inner2: given Vec[Int] = new Vec[Int](array_new[Int](2), 0);
                inner2!push[![inner2]](300);

                let outer: given Vec[Vec[Int]] = new Vec[Vec[Int]](array_new[Vec[Int]](4), 0);
                outer!push[![outer]](inner0→);
                outer!push[![outer]](inner1→);
                outer!push[![outer]](inner2→);

                let got: given Vec[Int] = outer→get[given](1);
                print(got.len→);
                ();
            }
        }
    "#,
        expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_inner0 : given Vec[Int] = new Vec [Int] (array_new [Int](2), 0) ;
        Output: Trace:   _1_inner0 = Vec { data: Array { flag: Given, rc: 1, ⚡, ⚡ }, len: 0 }
        Output: Trace:   _1_inner0 ! . push [! [_1_inner0]] (100) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Int, ! [_2_self . data]](_2_self . data ! , _2_self . len → , _2_value →) ;
        Output: Trace:     _2_self . len = _2_self . len → + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_inner1 : given Vec[Int] = new Vec [Int] (array_new [Int](2), 0) ;
        Output: Trace:   _1_inner1 = Vec { data: Array { flag: Given, rc: 1, ⚡, ⚡ }, len: 0 }
        Output: Trace:   _1_inner1 ! . push [! [_1_inner1]] (200) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Int, ! [_3_self . data]](_3_self . data ! , _3_self . len → , _3_value →) ;
        Output: Trace:     _3_self . len = _3_self . len → + 1 ;
        Output: Trace:     _3_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_inner2 : given Vec[Int] = new Vec [Int] (array_new [Int](2), 0) ;
        Output: Trace:   _1_inner2 = Vec { data: Array { flag: Given, rc: 1, ⚡, ⚡ }, len: 0 }
        Output: Trace:   _1_inner2 ! . push [! [_1_inner2]] (300) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Int, ! [_4_self . data]](_4_self . data ! , _4_self . len → , _4_value →) ;
        Output: Trace:     _4_self . len = _4_self . len → + 1 ;
        Output: Trace:     _4_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_outer : given Vec[Vec[Int]] = new Vec [Vec[Int]] (array_new [Vec[Int]](4), 0) ;
        Output: Trace:   _1_outer = Vec { data: Array { flag: Given, rc: 1, Vec { data: ⚡, len: ⚡ }, Vec { data: ⚡, len: ⚡ }, Vec { data: ⚡, len: ⚡ }, Vec { data: ⚡, len: ⚡ } }, len: 0 }
        Output: Trace:   _1_outer ! . push [! [_1_outer]] (_1_inner0 →) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Vec[Int], ! [_5_self . data]](_5_self . data ! , _5_self . len → , _5_value →) ;
        Output: Trace:     _5_self . len = _5_self . len → + 1 ;
        Output: Trace:     _5_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_outer ! . push [! [_1_outer]] (_1_inner1 →) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Vec[Int], ! [_6_self . data]](_6_self . data ! , _6_self . len → , _6_value →) ;
        Output: Trace:     _6_self . len = _6_self . len → + 1 ;
        Output: Trace:     _6_self . len = 2
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_outer ! . push [! [_1_outer]] (_1_inner2 →) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Vec[Int], ! [_7_self . data]](_7_self . data ! , _7_self . len → , _7_value →) ;
        Output: Trace:     _7_self . len = _7_self . len → + 1 ;
        Output: Trace:     _7_self . len = 3
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_got : given Vec[Int] = _1_outer → . get [given] (1) ;
        Output: Trace:   enter Vec.get
        Output: Trace:     let _8_data : given [_8_self . data] Array[Vec[Int]] = _8_self . data → ;
        Output: Trace:     _8_data = Array { flag: Given, rc: 1, Vec { data: Array { flag: Given, rc: 1, 100, ⚡ }, len: 1 }, Vec { data: Array { flag: Given, rc: 1, 200, ⚡ }, len: 1 }, Vec { data: Array { flag: Given, rc: 1, 300, ⚡ }, len: 1 }, Vec { data: ⚡, len: ⚡ } }
        Output: Trace:     let _8_len : Int = _8_self . len → ;
        Output: Trace:     _8_len = 3
        Output: Trace:     array_drop [Vec[Int], given [_8_self], shared [_8_data]](_8_data . share , 0 , _8_index →) ;
        Output: Trace:     drop Vec
        Output: Trace:       if is_last_ref [shared [self . data]](self . data . share) { array_drop [Int, given, shared [self . data]](self . data . share , 0 , self . len →) ; } else { () ; } ;
        Output: Trace:       array_drop [Int, given, shared [self . data]](self . data . share , 0 , self . len →) ;
        Output: Trace:     array_drop [Vec[Int], given [_8_self], shared [_8_data]](_8_data . share , _8_index → + 1 , _8_len →) ;
        Output: Trace:     drop Vec
        Output: Trace:       if is_last_ref [shared [self . data]](self . data . share) { array_drop [Int, given, shared [self . data]](self . data . share , 0 , self . len →) ; } else { () ; } ;
        Output: Trace:       array_drop [Int, given, shared [self . data]](self . data . share , 0 , self . len →) ;
        Output: Trace:     array_give [Vec[Int], given [_8_self], shared [_8_data]](_8_data . share , _8_index →) ;
        Output: Trace:   exit Vec.get => Vec { data: Array { flag: Given, rc: 1, 200, ⚡ }, len: 1 }
        Output: Trace:   _1_got = Vec { data: Array { flag: Given, rc: 1, 200, ⚡ }, len: 1 }
        Output: Trace:   print(_1_got . len →) ;
        Output: ----->   1
        Output: Trace:   () ;
        Output: Trace:   drop Vec
        Output: Trace:     if is_last_ref [shared [self . data]](self . data . share) { array_drop [Int, given, shared [self . data]](self . data . share , 0 , self . len →) ; } else { () ; } ;
        Output: Trace:     array_drop [Int, given, shared [self . data]](self . data . share , 0 , self . len →) ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]
    );
}

// ---------------------------------------------------------------
// Edge case: mut reference to flat class element through Vec
// ---------------------------------------------------------------

#[test]
fn vec_mut_ref_to_flat_element() {
    // array_give with P=mut on a flat Data class.
    // Returns a Lease pointing into the array backing.
    vec_test!(
        r#"
        struct Data {
            x: Int;
        }

        struct Main {
            fn main(given self) → () {
                let v: given Vec[Data] = new Vec[Data](array_new[Data](4), 0);
                v!push[![v]](new Data(42));
                let elem: ![v.data] Data = array_give[Data, ![v.data], shared[v.data]](v.data.share, 0);
                print(elem.x→);
                ();
            }
        }
    "#,
        expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_v : given Vec[Data] = new Vec [Data] (array_new [Data](4), 0) ;
        Output: Trace:   _1_v = Vec { data: Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ }, Data { x: ⚡ }, Data { x: ⚡ } }, len: 0 }
        Output: Trace:   _1_v ! . push [! [_1_v]] (new Data (42)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Data, ! [_2_self . data]](_2_self . data ! , _2_self . len → , _2_value →) ;
        Output: Trace:     _2_self . len = _2_self . len → + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_elem : ! [_1_v . data] Data = array_give [Data, ! [_1_v . data], shared [_1_v . data]](_1_v . data . share , 0) ;
        Output: Trace:   _1_elem = ! [_1_v . data] Data { x: 42 }
        Output: Trace:   print(_1_elem . x →) ;
        Output: ----->   42
        Output: Trace:   () ;
        Output: Trace:   drop Vec
        Output: Trace:     if is_last_ref [shared [self . data]](self . data . share) { array_drop [Data, given, shared [self . data]](self . data . share , 0 , self . len →) ; } else { () ; } ;
        Output: Trace:     array_drop [Data, given, shared [self . data]](self . data . share , 0 , self . len →) ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]
    );
}

// ---------------------------------------------------------------
// Edge case: mut reference to boxed element through Vec
// ---------------------------------------------------------------

#[test]
fn vec_mut_ref_to_boxed_element() {
    // array_give with P=mut on a boxed Array[Int] element.
    // Returns a Lease to the inner array's data.
    vec_test!(
        r#"
        struct Main {
            fn main(given self) → () {
                let outer: given Vec[Array[Int]] = new Vec[Array[Int]](array_new[Array[Int]](4), 0);
                let inner: given Array[Int] = array_new[Int](2);
                array_write[Int, ![inner]](inner!, 0, 99);
                outer!push[![outer]](inner→);
                let elem: ![outer.data] Array[Int] = array_give[Array[Int], ![outer.data], shared[outer.data]](outer.data.share, 0);
                print(array_give[Int, given, shared[elem]](elem.share, 0));
                ();
            }
        }
    "#,
        expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_outer : given Vec[Array[Int]] = new Vec [Array[Int]] (array_new [Array[Int]](4), 0) ;
        Output: Trace:   _1_outer = Vec { data: Array { flag: Given, rc: 1, ⚡, ⚡, ⚡, ⚡ }, len: 0 }
        Output: Trace:   let _1_inner : given Array[Int] = array_new [Int](2) ;
        Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡, ⚡ }
        Output: Trace:   array_write [Int, ! [_1_inner]](_1_inner ! , 0 , 99) ;
        Output: Trace:   _1_outer ! . push [! [_1_outer]] (_1_inner →) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Array[Int], ! [_2_self . data]](_2_self . data ! , _2_self . len → , _2_value →) ;
        Output: Trace:     _2_self . len = _2_self . len → + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_elem : ! [_1_outer . data] Array[Int] = array_give [Array[Int], ! [_1_outer . data], shared [_1_outer . data]](_1_outer . data . share , 0) ;
        Output: Trace:   _1_elem = ! [_1_outer . data] <unexpected: RefCount(1)>
        Output: Trace:   print(array_give [Int, given, shared [_1_elem]](_1_elem . share , 0)) ;
        Output: ----->   99
        Output: Trace:   () ;
        Output: Trace:   drop Vec
        Output: Trace:     if is_last_ref [shared [self . data]](self . data . share) { array_drop [Array[Int], given, shared [self . data]](self . data . share , 0 , self . len →) ; } else { () ; } ;
        Output: Trace:     array_drop [Array[Int], given, shared [self . data]](self . data . share , 0 , self . len →) ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]
    );
}

// ---------------------------------------------------------------
// Bug demonstration: Vec.get with P=![v]
// ---------------------------------------------------------------

/// Calls Vec.get through a mut place sharing. Inside the method body, P is
/// substituted to ![v], and array_give receives given[self]
/// where self: ![v] Vec[Data]. perm_to_operms must classify
/// given[self] as Lease, which requires resolving through
/// self → ![v] → v (a caller-scope variable).
///
/// EXPECTED: elem should be a mut place sharing to the array element.
/// CURRENT BUG: prove_is_mut fails because v is not in the method's
/// env, so perm_to_operms falls through to SharedPlace, producing a
/// copied-out value instead of a Lease into the array.
/// Regression test: `v!get[![v]](0)` must return a Lease into the
/// array, not a borrowed copy. Previously failed because `perm_to_operms`
/// couldn't resolve caller-scope places (e.g., `v` in `![v]`) inside the
/// method's env. Fixed by Phase 3 (fresh names + caller env extension).
#[test]
fn vec_get_through_mut_ref() {
    vec_test!(
        r#"
        struct Data {
            x: Int;
        }

        struct Main {
            fn main(given self) → () {
                let v: given Vec[Data] = new Vec[Data](array_new[Data](4), 0);
                v!push[![v]](new Data(42));
                let elem = v!get[![v]](0);
                print(elem.x→);
                ();
            }
        }
    "#,
        expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_v : given Vec[Data] = new Vec [Data] (array_new [Data](4), 0) ;
        Output: Trace:   _1_v = Vec { data: Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ }, Data { x: ⚡ }, Data { x: ⚡ } }, len: 0 }
        Output: Trace:   _1_v ! . push [! [_1_v]] (new Data (42)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Data, ! [_2_self . data]](_2_self . data ! , _2_self . len → , _2_value →) ;
        Output: Trace:     _2_self . len = _2_self . len → + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_elem = _1_v ! . get [! [_1_v]] (0) ;
        Output: Trace:   enter Vec.get
        Output: Trace:     let _3_data : given [_3_self . data] Array[Data] = _3_self . data → ;
        Output: Trace:     _3_data = ! [_1_v] <unexpected: RefCount(1)>
        Output: Trace:     let _3_len : Int = _3_self . len → ;
        Output: Trace:     _3_len = 1
        Output: Trace:     array_drop [Data, given [_3_self], shared [_3_data]](_3_data . share , 0 , _3_index →) ;
        Output: Trace:     array_drop [Data, given [_3_self], shared [_3_data]](_3_data . share , _3_index → + 1 , _3_len →) ;
        Output: Trace:     array_give [Data, given [_3_self], shared [_3_data]](_3_data . share , _3_index →) ;
        Output: Trace:   exit Vec.get => ! [_1_v] Data { x: 42 }
        Output: Trace:   _1_elem = ! [_1_v] Data { x: 42 }
        Output: Trace:   print(_1_elem . x →) ;
        Output: ----->   42
        Output: Trace:   () ;
        Output: Trace:   drop Vec
        Output: Trace:     if is_last_ref [shared [self . data]](self . data . share) { array_drop [Data, given, shared [self . data]](self . data . share , 0 , self . len →) ; } else { () ; } ;
        Output: Trace:     array_drop [Data, given, shared [self . data]](self . data . share , 0 , self . len →) ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]]
    );
}

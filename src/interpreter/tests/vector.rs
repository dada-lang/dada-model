/// Tests for Vec and Iterator — the capstone integration tests (Phase 5).
///
/// These tests exercise the full stack: classes with drop bodies, is_last_ref,
/// array intrinsics with poly-permission dispatch, and whole-place drop semantics.
///
/// These tests exercise the full stack with the type checker and interpreter.

/// Returns the standard Vec and Iterator class definitions from the design doc.
///
/// Design note on Iterator.drop: no `is_last_ref` guard is needed (unlike Vec.drop)
/// because the poly-permission `P` already handles all cases correctly:
///   - P=given:  `array_drop` drops remaining elements (we own them)
///   - P=shared: `array_drop` is a no-op (we don't own them)
///   - P=ref:    `array_drop` is a no-op (we don't own them)
/// Vec.drop needs `is_last_ref` because it runs on *every* handle drop (shared
/// handles each trigger the drop body), but Iterator.drop's `array_drop[T, P, ...]`
/// naturally dispatches on the permission the iterator was created with.
fn vec_prelude() -> &'static str {
    r#"
    class Vec[ty T] {
        data: Array[T];
        len: Int;

        fn push[perm P](P self, value: given T) -> ()
        where
            P is mut,
        {
            array_write[T, mut[self.data]](self.data.mut, self.len.give, value.give);
            self.len = self.len.give + 1;
            ();
        }

        fn get[perm P](P self, index: Int) -> given[self] T {
            let data: given[self.data] Array[T] = self.data.give;
            let len: Int = self.len.give;
            array_drop[T, given[self], ref[data]](data.ref, 0, index.give);
            array_drop[T, given[self], ref[data]](data.ref, index.give + 1, len.give);
            array_give[T, given[self], ref[data]](data.ref, index.give);
        }

        fn iter[perm P](P self) -> Iterator[P, T] {
            new Iterator[P, T](self.give, 0);
        }

        drop {
            if is_last_ref[ref[self.data]](self.data.ref) {
                array_drop[T, given, ref[self.data]](self.data.ref, 0, self.len.give);
            } else {
                ();
            };
        }
    }

    class Iterator[perm P, ty T]
    where
        T is relative,
    {
        vec: P Vec[T];
        start: Int;

        fn next[perm I](I self) -> P T
        where
            I is mut,
        {
            let index: Int = self.start.give;
            self.start = self.start.give + 1;
            array_give[T, P, ref[self.vec.data]](self.vec.data.ref, index.give);
        }

        drop {
            let data: given[self.vec.data] Array[T] = self.vec.data.give;
            let start: Int = self.start.give;
            let len: Int = self.vec.len.give;
            array_drop[T, P, ref[data]](data.ref, start.give, len.give);
        }
    }
    "#
}

// ---------------------------------------------------------------
// Vec push basics
// ---------------------------------------------------------------

#[test]
fn vec_push_increments_len() {
    crate::assert_interpret!(prefix: vec_prelude(),
        {
        class Main {
            fn main(given self) -> () {
                let v: given Vec[Int] = new Vec[Int](array_new[Int](4), 0);
                v.mut.push[mut[v]](42);
                print(v.len.give);
                ();
            }
        }
    },
        type: ok, interpret: ok(expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_v : given Vec[Int] = new Vec [Int] (array_new [Int](4), 0) ;
        Output: Trace:   _1_v = Vec { data: Array { flag: Given, rc: 1, ⚡, ⚡, ⚡, ⚡ }, len: 0 }
        Output: Trace:   _1_v . mut . push [mut [_1_v]] (42) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Int, mut [_2_self . data]](_2_self . data . mut , _2_self . len . give , _2_value . give) ;
        Output: Trace:     _2_self . len = _2_self . len . give + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   print(_1_v . len . give) ;
        Output: ----->   1
        Output: Trace:   () ;
        Output: Trace:   drop Vec
        Output: Trace:     if is_last_ref [ref [self . data]](self . data . ref) { array_drop [Int, given, ref [self . data]](self . data . ref , 0 , self . len . give) ; } else { () ; } ;
        Output: Trace:     array_drop [Int, given, ref [self . data]](self . data . ref , 0 , self . len . give) ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]])
    );
}

// ---------------------------------------------------------------
// Vec push + get with P=given (move semantics)
// ---------------------------------------------------------------

#[test]
fn vec_push_and_get_given() {
    // Push 3 elements, then get(1) with P=given.
    // Drops elements 0 and 2, returns element 1.
    crate::assert_interpret!(prefix: vec_prelude(),
        {
        class Data {
            value: Int;

            drop {
                print(self.value.give);
            }
        }

        class Main {
            fn main(given self) -> () {
                let v: given Vec[Data] = new Vec[Data](array_new[Data](4), 0);
                v.mut.push[mut[v]](new Data(10));
                v.mut.push[mut[v]](new Data(20));
                v.mut.push[mut[v]](new Data(30));
                let got: given Data = v.give.get[given](1);
                print(got.value.give);
                ();
            }
        }
    },
        type: ok, interpret: ok(expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_v : given Vec[Data] = new Vec [Data] (array_new [Data](4), 0) ;
        Output: Trace:   _1_v = Vec { data: Array { flag: Given, rc: 1, Data { value: ⚡ }, Data { value: ⚡ }, Data { value: ⚡ }, Data { value: ⚡ } }, len: 0 }
        Output: Trace:   _1_v . mut . push [mut [_1_v]] (new Data (10)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Data, mut [_2_self . data]](_2_self . data . mut , _2_self . len . give , _2_value . give) ;
        Output: Trace:     _2_self . len = _2_self . len . give + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_v . mut . push [mut [_1_v]] (new Data (20)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Data, mut [_3_self . data]](_3_self . data . mut , _3_self . len . give , _3_value . give) ;
        Output: Trace:     _3_self . len = _3_self . len . give + 1 ;
        Output: Trace:     _3_self . len = 2
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_v . mut . push [mut [_1_v]] (new Data (30)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Data, mut [_4_self . data]](_4_self . data . mut , _4_self . len . give , _4_value . give) ;
        Output: Trace:     _4_self . len = _4_self . len . give + 1 ;
        Output: Trace:     _4_self . len = 3
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_got : given Data = _1_v . give . get [given] (1) ;
        Output: Trace:   enter Vec.get
        Output: Trace:     let _5_data : given [_5_self . data] Array[Data] = _5_self . data . give ;
        Output: Trace:     _5_data = Array { flag: Given, rc: 1, Data { value: 10 }, Data { value: 20 }, Data { value: 30 }, Data { value: ⚡ } }
        Output: Trace:     let _5_len : Int = _5_self . len . give ;
        Output: Trace:     _5_len = 3
        Output: Trace:     array_drop [Data, given [_5_self], ref [_5_data]](_5_data . ref , 0 , _5_index . give) ;
        Output: Trace:     drop Data
        Output: Trace:       print(self . value . give) ;
        Output: ----->       10
        Output: Trace:     array_drop [Data, given [_5_self], ref [_5_data]](_5_data . ref , _5_index . give + 1 , _5_len . give) ;
        Output: Trace:     drop Data
        Output: Trace:       print(self . value . give) ;
        Output: ----->       30
        Output: Trace:     array_give [Data, given [_5_self], ref [_5_data]](_5_data . ref , _5_index . give) ;
        Output: Trace:   exit Vec.get => Data { value: 20 }
        Output: Trace:   _1_got = Data { value: 20 }
        Output: Trace:   print(_1_got . value . give) ;
        Output: ----->   20
        Output: Trace:   () ;
        Output: Trace:   drop Data
        Output: Trace:     print(self . value . give) ;
        Output: ----->     20
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]])
    );
}

// ---------------------------------------------------------------
// Vec drop cleans all elements
// ---------------------------------------------------------------

#[test]
fn vec_drop_cleans_all_elements() {
    crate::assert_interpret!(prefix: vec_prelude(),
        {
        class Item {
            val: Int;

            drop {
                print(self.val.give);
            }
        }

        class Main {
            fn main(given self) -> () {
                let v: given Vec[Item] = new Vec[Item](array_new[Item](4), 0);
                v.mut.push[mut[v]](new Item(100));
                v.mut.push[mut[v]](new Item(200));
                v.mut.push[mut[v]](new Item(300));
                ();
            }
        }
    },
        type: ok, interpret: ok(expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_v : given Vec[Item] = new Vec [Item] (array_new [Item](4), 0) ;
        Output: Trace:   _1_v = Vec { data: Array { flag: Given, rc: 1, Item { val: ⚡ }, Item { val: ⚡ }, Item { val: ⚡ }, Item { val: ⚡ } }, len: 0 }
        Output: Trace:   _1_v . mut . push [mut [_1_v]] (new Item (100)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Item, mut [_2_self . data]](_2_self . data . mut , _2_self . len . give , _2_value . give) ;
        Output: Trace:     _2_self . len = _2_self . len . give + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_v . mut . push [mut [_1_v]] (new Item (200)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Item, mut [_3_self . data]](_3_self . data . mut , _3_self . len . give , _3_value . give) ;
        Output: Trace:     _3_self . len = _3_self . len . give + 1 ;
        Output: Trace:     _3_self . len = 2
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_v . mut . push [mut [_1_v]] (new Item (300)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Item, mut [_4_self . data]](_4_self . data . mut , _4_self . len . give , _4_value . give) ;
        Output: Trace:     _4_self . len = _4_self . len . give + 1 ;
        Output: Trace:     _4_self . len = 3
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   () ;
        Output: Trace:   drop Vec
        Output: Trace:     if is_last_ref [ref [self . data]](self . data . ref) { array_drop [Item, given, ref [self . data]](self . data . ref , 0 , self . len . give) ; } else { () ; } ;
        Output: Trace:     array_drop [Item, given, ref [self . data]](self . data . ref , 0 , self . len . give) ;
        Output: Trace:     drop Item
        Output: Trace:       print(self . val . give) ;
        Output: ----->       100
        Output: Trace:     drop Item
        Output: Trace:       print(self . val . give) ;
        Output: ----->       200
        Output: Trace:     drop Item
        Output: Trace:       print(self . val . give) ;
        Output: ----->       300
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]])
    );
}

// ---------------------------------------------------------------
// Vec iter and next (given permission, consuming)
// ---------------------------------------------------------------

#[test]
fn vec_iter_and_next() {
    // Consuming iterator: next() moves element 0, drop cleans 1 and 2.
    crate::assert_interpret!(prefix: vec_prelude(),
        {
        class Item {
            val: Int;

            drop {
                print(self.val.give);
            }
        }

        class Main {
            fn main(given self) -> () {
                let v: given Vec[Item] = new Vec[Item](array_new[Item](4), 0);
                v.mut.push[mut[v]](new Item(10));
                v.mut.push[mut[v]](new Item(20));
                v.mut.push[mut[v]](new Item(30));
                let it: Iterator[given, Item] = v.give.iter[given]();
                let first: given Item = it.mut.next[mut[it]]();
                print(first.val.give);
                ();
            }
        }
    },
        type: ok, interpret: ok(expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_v : given Vec[Item] = new Vec [Item] (array_new [Item](4), 0) ;
        Output: Trace:   _1_v = Vec { data: Array { flag: Given, rc: 1, Item { val: ⚡ }, Item { val: ⚡ }, Item { val: ⚡ }, Item { val: ⚡ } }, len: 0 }
        Output: Trace:   _1_v . mut . push [mut [_1_v]] (new Item (10)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Item, mut [_2_self . data]](_2_self . data . mut , _2_self . len . give , _2_value . give) ;
        Output: Trace:     _2_self . len = _2_self . len . give + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_v . mut . push [mut [_1_v]] (new Item (20)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Item, mut [_3_self . data]](_3_self . data . mut , _3_self . len . give , _3_value . give) ;
        Output: Trace:     _3_self . len = _3_self . len . give + 1 ;
        Output: Trace:     _3_self . len = 2
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_v . mut . push [mut [_1_v]] (new Item (30)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Item, mut [_4_self . data]](_4_self . data . mut , _4_self . len . give , _4_value . give) ;
        Output: Trace:     _4_self . len = _4_self . len . give + 1 ;
        Output: Trace:     _4_self . len = 3
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_it : Iterator[given, Item] = _1_v . give . iter [given] () ;
        Output: Trace:   enter Vec.iter
        Output: Trace:     new Iterator [given, Item] (_5_self . give, 0) ;
        Output: Trace:   exit Vec.iter => Iterator { vec: Vec { data: Array { flag: Given, rc: 1, Item { val: 10 }, Item { val: 20 }, Item { val: 30 }, Item { val: ⚡ } }, len: 3 }, start: 0 }
        Output: Trace:   _1_it = Iterator { vec: Vec { data: Array { flag: Given, rc: 1, Item { val: 10 }, Item { val: 20 }, Item { val: 30 }, Item { val: ⚡ } }, len: 3 }, start: 0 }
        Output: Trace:   let _1_first : given Item = _1_it . mut . next [mut [_1_it]] () ;
        Output: Trace:   enter Iterator.next
        Output: Trace:     let _6_index : Int = _6_self . start . give ;
        Output: Trace:     _6_index = 0
        Output: Trace:     _6_self . start = _6_self . start . give + 1 ;
        Output: Trace:     _6_self . start = 1
        Output: Trace:     array_give [Item, given, ref [_6_self . vec . data]](_6_self . vec . data . ref , _6_index . give) ;
        Output: Trace:   exit Iterator.next => Item { val: 10 }
        Output: Trace:   _1_first = Item { val: 10 }
        Output: Trace:   print(_1_first . val . give) ;
        Output: ----->   10
        Output: Trace:   () ;
        Output: Trace:   drop Item
        Output: Trace:     print(self . val . give) ;
        Output: ----->     10
        Output: Trace:   drop Iterator
        Output: Trace:     let data : given [self . vec . data] Array[Item] = self . vec . data . give ;
        Output: Trace:     data = ref [@ magic] Array { flag: Borrowed, rc: 1, Item { val: ⚡ }, Item { val: 20 }, Item { val: 30 }, Item { val: ⚡ } }
        Output: Trace:     let start : Int = self . start . give ;
        Output: Trace:     start = 1
        Output: Trace:     let len : Int = self . vec . len . give ;
        Output: Trace:     len = 3
        Output: Trace:     array_drop [Item, given, ref [data]](data . ref , start . give , len . give) ;
        Output: Trace:     drop Item
        Output: Trace:       print(self . val . give) ;
        Output: ----->       20
        Output: Trace:     drop Item
        Output: Trace:       print(self . val . give) ;
        Output: ----->       30
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]])
    );
}

// ---------------------------------------------------------------
// Shared Vec get (P=shared, non-consuming)
// ---------------------------------------------------------------

#[test]
fn shared_vec_get() {
    // P=shared: array_drop is no-op, array_give copies.
    crate::assert_interpret!(prefix: vec_prelude(),
        {
        class Data {
            value: Int;
        }

        class Main {
            fn main(given self) -> () {
                let v: given Vec[Data] = new Vec[Data](array_new[Data](4), 0);
                v.mut.push[mut[v]](new Data(10));
                v.mut.push[mut[v]](new Data(20));
                let sv: shared Vec[Data] = v.give.share;
                let got: shared Data = sv.give.get[shared](0);
                print(got.give);
                ();
            }
        }
    },
        type: ok, interpret: ok(expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_v : given Vec[Data] = new Vec [Data] (array_new [Data](4), 0) ;
        Output: Trace:   _1_v = Vec { data: Array { flag: Given, rc: 1, Data { value: ⚡ }, Data { value: ⚡ }, Data { value: ⚡ }, Data { value: ⚡ } }, len: 0 }
        Output: Trace:   _1_v . mut . push [mut [_1_v]] (new Data (10)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Data, mut [_2_self . data]](_2_self . data . mut , _2_self . len . give , _2_value . give) ;
        Output: Trace:     _2_self . len = _2_self . len . give + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_v . mut . push [mut [_1_v]] (new Data (20)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Data, mut [_3_self . data]](_3_self . data . mut , _3_self . len . give , _3_value . give) ;
        Output: Trace:     _3_self . len = _3_self . len . give + 1 ;
        Output: Trace:     _3_self . len = 2
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_sv : shared Vec[Data] = _1_v . give . share ;
        Output: Trace:   _1_sv = shared Vec { data: Array { flag: Shared, rc: 1, Data { value: 10 }, Data { value: 20 }, Data { value: ⚡ }, Data { value: ⚡ } }, len: 2 }
        Output: Trace:   let _1_got : shared Data = _1_sv . give . get [shared] (0) ;
        Output: Trace:   enter Vec.get
        Output: Trace:     let _4_data : given [_4_self . data] Array[Data] = _4_self . data . give ;
        Output: Trace:     _4_data = shared Array { flag: Shared, rc: 3, Data { value: 10 }, Data { value: 20 }, Data { value: ⚡ }, Data { value: ⚡ } }
        Output: Trace:     let _4_len : Int = _4_self . len . give ;
        Output: Trace:     _4_len = 2
        Output: Trace:     array_drop [Data, given [_4_self], ref [_4_data]](_4_data . ref , 0 , _4_index . give) ;
        Output: Trace:     array_drop [Data, given [_4_self], ref [_4_data]](_4_data . ref , _4_index . give + 1 , _4_len . give) ;
        Output: Trace:     array_give [Data, given [_4_self], ref [_4_data]](_4_data . ref , _4_index . give) ;
        Output: Trace:     drop Vec
        Output: Trace:       if is_last_ref [ref [self . data]](self . data . ref) { array_drop [Data, given, ref [self . data]](self . data . ref , 0 , self . len . give) ; } else { () ; } ;
        Output: Trace:       () ;
        Output: Trace:   exit Vec.get => shared Data { value: 10 }
        Output: Trace:   _1_got = shared Data { value: 10 }
        Output: Trace:   print(_1_got . give) ;
        Output: ----->   shared Data { value: 10 }
        Output: Trace:   () ;
        Output: Trace:   drop Vec
        Output: Trace:     if is_last_ref [ref [self . data]](self . data . ref) { array_drop [Data, given, ref [self . data]](self . data . ref , 0 , self . len . give) ; } else { () ; } ;
        Output: Trace:     array_drop [Data, given, ref [self . data]](self . data . ref , 0 , self . len . give) ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]])
    );
}

// ---------------------------------------------------------------
// Ref Vec get (P=ref, borrowing)
// ---------------------------------------------------------------

#[test]
fn ref_vec_get() {
    // P=ref: elements are borrows, Vec remains intact.
    crate::assert_interpret!(prefix: vec_prelude(),
        {
        class Data {
            value: Int;
        }

        class Main {
            fn main(given self) -> () {
                let v: given Vec[Data] = new Vec[Data](array_new[Data](4), 0);
                v.mut.push[mut[v]](new Data(10));
                v.mut.push[mut[v]](new Data(20));
                let got: ref[v] Data = v.ref.get[ref[v]](1);
                print(got.value.give);
                ();
            }
        }
    },
        type: ok, interpret: ok(expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_v : given Vec[Data] = new Vec [Data] (array_new [Data](4), 0) ;
        Output: Trace:   _1_v = Vec { data: Array { flag: Given, rc: 1, Data { value: ⚡ }, Data { value: ⚡ }, Data { value: ⚡ }, Data { value: ⚡ } }, len: 0 }
        Output: Trace:   _1_v . mut . push [mut [_1_v]] (new Data (10)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Data, mut [_2_self . data]](_2_self . data . mut , _2_self . len . give , _2_value . give) ;
        Output: Trace:     _2_self . len = _2_self . len . give + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_v . mut . push [mut [_1_v]] (new Data (20)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Data, mut [_3_self . data]](_3_self . data . mut , _3_self . len . give , _3_value . give) ;
        Output: Trace:     _3_self . len = _3_self . len . give + 1 ;
        Output: Trace:     _3_self . len = 2
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_got : ref [_1_v] Data = _1_v . ref . get [ref [_1_v]] (1) ;
        Output: Trace:   enter Vec.get
        Output: Trace:     let _4_data : given [_4_self . data] Array[Data] = _4_self . data . give ;
        Output: Trace:     _4_data = ref [_1_v] Array { flag: Borrowed, rc: 1, Data { value: 10 }, Data { value: 20 }, Data { value: ⚡ }, Data { value: ⚡ } }
        Output: Trace:     let _4_len : Int = _4_self . len . give ;
        Output: Trace:     _4_len = 2
        Output: Trace:     array_drop [Data, given [_4_self], ref [_4_data]](_4_data . ref , 0 , _4_index . give) ;
        Output: Trace:     array_drop [Data, given [_4_self], ref [_4_data]](_4_data . ref , _4_index . give + 1 , _4_len . give) ;
        Output: Trace:     array_give [Data, given [_4_self], ref [_4_data]](_4_data . ref , _4_index . give) ;
        Output: Trace:   exit Vec.get => ref [_1_v] Data { value: 20 }
        Output: Trace:   _1_got = ref [_1_v] Data { value: 20 }
        Output: Trace:   print(_1_got . value . give) ;
        Output: ----->   20
        Output: Trace:   () ;
        Output: Trace:   drop Vec
        Output: Trace:     if is_last_ref [ref [self . data]](self . data . ref) { array_drop [Data, given, ref [self . data]](self . data . ref , 0 , self . len . give) ; } else { () ; } ;
        Output: Trace:     array_drop [Data, given, ref [self . data]](self . data . ref , 0 , self . len . give) ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]])
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
    crate::assert_interpret!(prefix: vec_prelude(),
        {
        class Main {
            fn main(given self) -> () {
                let inner0: given Vec[Int] = new Vec[Int](array_new[Int](2), 0);
                inner0.mut.push[mut[inner0]](100);

                let inner1: given Vec[Int] = new Vec[Int](array_new[Int](2), 0);
                inner1.mut.push[mut[inner1]](200);

                let inner2: given Vec[Int] = new Vec[Int](array_new[Int](2), 0);
                inner2.mut.push[mut[inner2]](300);

                let outer: given Vec[Vec[Int]] = new Vec[Vec[Int]](array_new[Vec[Int]](4), 0);
                outer.mut.push[mut[outer]](inner0.give);
                outer.mut.push[mut[outer]](inner1.give);
                outer.mut.push[mut[outer]](inner2.give);

                let got: given Vec[Int] = outer.give.get[given](1);
                print(got.len.give);
                ();
            }
        }
    },
        type: ok, interpret: ok(expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_inner0 : given Vec[Int] = new Vec [Int] (array_new [Int](2), 0) ;
        Output: Trace:   _1_inner0 = Vec { data: Array { flag: Given, rc: 1, ⚡, ⚡ }, len: 0 }
        Output: Trace:   _1_inner0 . mut . push [mut [_1_inner0]] (100) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Int, mut [_2_self . data]](_2_self . data . mut , _2_self . len . give , _2_value . give) ;
        Output: Trace:     _2_self . len = _2_self . len . give + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_inner1 : given Vec[Int] = new Vec [Int] (array_new [Int](2), 0) ;
        Output: Trace:   _1_inner1 = Vec { data: Array { flag: Given, rc: 1, ⚡, ⚡ }, len: 0 }
        Output: Trace:   _1_inner1 . mut . push [mut [_1_inner1]] (200) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Int, mut [_3_self . data]](_3_self . data . mut , _3_self . len . give , _3_value . give) ;
        Output: Trace:     _3_self . len = _3_self . len . give + 1 ;
        Output: Trace:     _3_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_inner2 : given Vec[Int] = new Vec [Int] (array_new [Int](2), 0) ;
        Output: Trace:   _1_inner2 = Vec { data: Array { flag: Given, rc: 1, ⚡, ⚡ }, len: 0 }
        Output: Trace:   _1_inner2 . mut . push [mut [_1_inner2]] (300) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Int, mut [_4_self . data]](_4_self . data . mut , _4_self . len . give , _4_value . give) ;
        Output: Trace:     _4_self . len = _4_self . len . give + 1 ;
        Output: Trace:     _4_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_outer : given Vec[Vec[Int]] = new Vec [Vec[Int]] (array_new [Vec[Int]](4), 0) ;
        Output: Trace:   _1_outer = Vec { data: Array { flag: Given, rc: 1, Vec { data: ⚡, len: ⚡ }, Vec { data: ⚡, len: ⚡ }, Vec { data: ⚡, len: ⚡ }, Vec { data: ⚡, len: ⚡ } }, len: 0 }
        Output: Trace:   _1_outer . mut . push [mut [_1_outer]] (_1_inner0 . give) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Vec[Int], mut [_5_self . data]](_5_self . data . mut , _5_self . len . give , _5_value . give) ;
        Output: Trace:     _5_self . len = _5_self . len . give + 1 ;
        Output: Trace:     _5_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_outer . mut . push [mut [_1_outer]] (_1_inner1 . give) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Vec[Int], mut [_6_self . data]](_6_self . data . mut , _6_self . len . give , _6_value . give) ;
        Output: Trace:     _6_self . len = _6_self . len . give + 1 ;
        Output: Trace:     _6_self . len = 2
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   _1_outer . mut . push [mut [_1_outer]] (_1_inner2 . give) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Vec[Int], mut [_7_self . data]](_7_self . data . mut , _7_self . len . give , _7_value . give) ;
        Output: Trace:     _7_self . len = _7_self . len . give + 1 ;
        Output: Trace:     _7_self . len = 3
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_got : given Vec[Int] = _1_outer . give . get [given] (1) ;
        Output: Trace:   enter Vec.get
        Output: Trace:     let _8_data : given [_8_self . data] Array[Vec[Int]] = _8_self . data . give ;
        Output: Trace:     _8_data = Array { flag: Given, rc: 1, Vec { data: Array { flag: Given, rc: 1, 100, ⚡ }, len: 1 }, Vec { data: Array { flag: Given, rc: 1, 200, ⚡ }, len: 1 }, Vec { data: Array { flag: Given, rc: 1, 300, ⚡ }, len: 1 }, Vec { data: ⚡, len: ⚡ } }
        Output: Trace:     let _8_len : Int = _8_self . len . give ;
        Output: Trace:     _8_len = 3
        Output: Trace:     array_drop [Vec[Int], given [_8_self], ref [_8_data]](_8_data . ref , 0 , _8_index . give) ;
        Output: Trace:     drop Vec
        Output: Trace:       if is_last_ref [ref [self . data]](self . data . ref) { array_drop [Int, given, ref [self . data]](self . data . ref , 0 , self . len . give) ; } else { () ; } ;
        Output: Trace:       array_drop [Int, given, ref [self . data]](self . data . ref , 0 , self . len . give) ;
        Output: Trace:     array_drop [Vec[Int], given [_8_self], ref [_8_data]](_8_data . ref , _8_index . give + 1 , _8_len . give) ;
        Output: Trace:     drop Vec
        Output: Trace:       if is_last_ref [ref [self . data]](self . data . ref) { array_drop [Int, given, ref [self . data]](self . data . ref , 0 , self . len . give) ; } else { () ; } ;
        Output: Trace:       array_drop [Int, given, ref [self . data]](self . data . ref , 0 , self . len . give) ;
        Output: Trace:     array_give [Vec[Int], given [_8_self], ref [_8_data]](_8_data . ref , _8_index . give) ;
        Output: Trace:   exit Vec.get => Vec { data: Array { flag: Given, rc: 1, 200, ⚡ }, len: 1 }
        Output: Trace:   _1_got = Vec { data: Array { flag: Given, rc: 1, 200, ⚡ }, len: 1 }
        Output: Trace:   print(_1_got . len . give) ;
        Output: ----->   1
        Output: Trace:   () ;
        Output: Trace:   drop Vec
        Output: Trace:     if is_last_ref [ref [self . data]](self . data . ref) { array_drop [Int, given, ref [self . data]](self . data . ref , 0 , self . len . give) ; } else { () ; } ;
        Output: Trace:     array_drop [Int, given, ref [self . data]](self . data . ref , 0 , self . len . give) ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]])
    );
}

// ---------------------------------------------------------------
// Edge case: mut reference to flat class element through Vec
// ---------------------------------------------------------------

#[test]
fn vec_mut_ref_to_flat_element() {
    // array_give with P=mut on a flat Data class.
    // Returns a MutRef pointing into the array backing.
    crate::assert_interpret!(prefix: vec_prelude(),
        {
        class Data {
            x: Int;
        }

        class Main {
            fn main(given self) -> () {
                let v: given Vec[Data] = new Vec[Data](array_new[Data](4), 0);
                v.mut.push[mut[v]](new Data(42));
                let elem: mut[v.data] Data = array_give[Data, mut[v.data], ref[v.data]](v.data.ref, 0);
                print(elem.x.give);
                ();
            }
        }
    },
        type: ok, interpret: ok(expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_v : given Vec[Data] = new Vec [Data] (array_new [Data](4), 0) ;
        Output: Trace:   _1_v = Vec { data: Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ }, Data { x: ⚡ }, Data { x: ⚡ } }, len: 0 }
        Output: Trace:   _1_v . mut . push [mut [_1_v]] (new Data (42)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Data, mut [_2_self . data]](_2_self . data . mut , _2_self . len . give , _2_value . give) ;
        Output: Trace:     _2_self . len = _2_self . len . give + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_elem : mut [_1_v . data] Data = array_give [Data, mut [_1_v . data], ref [_1_v . data]](_1_v . data . ref , 0) ;
        Output: Trace:   _1_elem = mut [_1_v . data] Data { x: 42 }
        Output: Trace:   print(_1_elem . x . give) ;
        Output: ----->   42
        Output: Trace:   () ;
        Output: Trace:   drop Vec
        Output: Trace:     if is_last_ref [ref [self . data]](self . data . ref) { array_drop [Data, given, ref [self . data]](self . data . ref , 0 , self . len . give) ; } else { () ; } ;
        Output: Trace:     array_drop [Data, given, ref [self . data]](self . data . ref , 0 , self . len . give) ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]])
    );
}

// ---------------------------------------------------------------
// Edge case: mut reference to boxed element through Vec
// ---------------------------------------------------------------

#[test]
fn vec_mut_ref_to_boxed_element() {
    // array_give with P=mut on a boxed Array[Int] element.
    // Returns a MutRef to the inner array's data.
    crate::assert_interpret!(prefix: vec_prelude(),
        {
        class Main {
            fn main(given self) -> () {
                let outer: given Vec[Array[Int]] = new Vec[Array[Int]](array_new[Array[Int]](4), 0);
                let inner: given Array[Int] = array_new[Int](2);
                array_write[Int, mut[inner]](inner.mut, 0, 99);
                outer.mut.push[mut[outer]](inner.give);
                let elem: mut[outer.data] Array[Int] = array_give[Array[Int], mut[outer.data], ref[outer.data]](outer.data.ref, 0);
                print(array_give[Int, given, ref[elem]](elem.ref, 0));
                ();
            }
        }
    },
        type: ok, interpret: ok(expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_outer : given Vec[Array[Int]] = new Vec [Array[Int]] (array_new [Array[Int]](4), 0) ;
        Output: Trace:   _1_outer = Vec { data: Array { flag: Given, rc: 1, ⚡, ⚡, ⚡, ⚡ }, len: 0 }
        Output: Trace:   let _1_inner : given Array[Int] = array_new [Int](2) ;
        Output: Trace:   _1_inner = Array { flag: Given, rc: 1, ⚡, ⚡ }
        Output: Trace:   array_write [Int, mut [_1_inner]](_1_inner . mut , 0 , 99) ;
        Output: Trace:   _1_outer . mut . push [mut [_1_outer]] (_1_inner . give) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Array[Int], mut [_2_self . data]](_2_self . data . mut , _2_self . len . give , _2_value . give) ;
        Output: Trace:     _2_self . len = _2_self . len . give + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_elem : mut [_1_outer . data] Array[Int] = array_give [Array[Int], mut [_1_outer . data], ref [_1_outer . data]](_1_outer . data . ref , 0) ;
        Output: Trace:   _1_elem = mut [_1_outer . data] <unexpected: RefCount(1)>
        Output: Trace:   print(array_give [Int, given, ref [_1_elem]](_1_elem . ref , 0)) ;
        Output: ----->   99
        Output: Trace:   () ;
        Output: Trace:   drop Vec
        Output: Trace:     if is_last_ref [ref [self . data]](self . data . ref) { array_drop [Array[Int], given, ref [self . data]](self . data . ref , 0 , self . len . give) ; } else { () ; } ;
        Output: Trace:     array_drop [Array[Int], given, ref [self . data]](self . data . ref , 0 , self . len . give) ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]])
    );
}

// ---------------------------------------------------------------
// Bug demonstration: Vec.get with P=mut[v]
// ---------------------------------------------------------------

/// Calls Vec.get through a mut ref. Inside the method body, P is
/// substituted to mut[v], and array_give receives given[self]
/// where self: mut[v] Vec[Data]. perm_to_operms must classify
/// given[self] as MutRef, which requires resolving through
/// self -> mut[v] -> v (a caller-scope variable).
///
/// EXPECTED: elem should be a mut ref to the array element.
/// CURRENT BUG: prove_is_mut fails because v is not in the method's
/// env, so perm_to_operms falls through to Borrowed, producing a
/// copied-out value instead of a MutRef into the array.
/// Regression test: `v.mut.get[mut[v]](0)` must return a MutRef into the
/// array, not a borrowed copy. Previously failed because `perm_to_operms`
/// couldn't resolve caller-scope places (e.g., `v` in `mut[v]`) inside the
/// method's env. Fixed by Phase 3 (fresh names + caller env extension).
#[test]
fn vec_get_through_mut_ref() {
    crate::assert_interpret!(prefix: vec_prelude(),
        {
        class Data {
            x: Int;
        }

        class Main {
            fn main(given self) -> () {
                let v: given Vec[Data] = new Vec[Data](array_new[Data](4), 0);
                v.mut.push[mut[v]](new Data(42));
                let elem = v.mut.get[mut[v]](0);
                print(elem.x.give);
                ();
            }
        }
    },
        type: ok, interpret: ok(expect_test::expect![[r#"
        Output: Trace: enter Main.main
        Output: Trace:   let _1_v : given Vec[Data] = new Vec [Data] (array_new [Data](4), 0) ;
        Output: Trace:   _1_v = Vec { data: Array { flag: Given, rc: 1, Data { x: ⚡ }, Data { x: ⚡ }, Data { x: ⚡ }, Data { x: ⚡ } }, len: 0 }
        Output: Trace:   _1_v . mut . push [mut [_1_v]] (new Data (42)) ;
        Output: Trace:   enter Vec.push
        Output: Trace:     array_write [Data, mut [_2_self . data]](_2_self . data . mut , _2_self . len . give , _2_value . give) ;
        Output: Trace:     _2_self . len = _2_self . len . give + 1 ;
        Output: Trace:     _2_self . len = 1
        Output: Trace:     () ;
        Output: Trace:   exit Vec.push => ()
        Output: Trace:   let _1_elem = _1_v . mut . get [mut [_1_v]] (0) ;
        Output: Trace:   enter Vec.get
        Output: Trace:     let _3_data : given [_3_self . data] Array[Data] = _3_self . data . give ;
        Output: Trace:     _3_data = mut [_1_v] <unexpected: RefCount(1)>
        Output: Trace:     let _3_len : Int = _3_self . len . give ;
        Output: Trace:     _3_len = 1
        Output: Trace:     array_drop [Data, given [_3_self], ref [_3_data]](_3_data . ref , 0 , _3_index . give) ;
        Output: Trace:     array_drop [Data, given [_3_self], ref [_3_data]](_3_data . ref , _3_index . give + 1 , _3_len . give) ;
        Output: Trace:     array_give [Data, given [_3_self], ref [_3_data]](_3_data . ref , _3_index . give) ;
        Output: Trace:   exit Vec.get => mut [_1_v] Data { x: 42 }
        Output: Trace:   _1_elem = mut [_1_v] Data { x: 42 }
        Output: Trace:   print(_1_elem . x . give) ;
        Output: ----->   42
        Output: Trace:   () ;
        Output: Trace:   drop Vec
        Output: Trace:     if is_last_ref [ref [self . data]](self . data . ref) { array_drop [Data, given, ref [self . data]](self . data . ref , 0 , self . len . give) ; } else { () ; } ;
        Output: Trace:     array_drop [Data, given, ref [self . data]](self . data . ref , 0 , self . len . give) ;
        Output: Trace: exit Main.main => ()
        Result: Ok: ()"#]])
    );
}

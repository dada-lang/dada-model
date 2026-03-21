/// Tests for Vec and Iterator — the capstone integration tests (Phase 5).
///
/// These tests exercise the full stack: classes with drop bodies, is_last_ref,
/// array intrinsics with poly-permission dispatch, and whole-place drop semantics.
///
/// All tests use assert_interpret_only! because the type checker doesn't yet
/// fully support the permission patterns used by Vec (e.g., `P self` with
/// generic perm, `given_from[self]` return types, etc.).

// ---------------------------------------------------------------
// Vec push basics
// ---------------------------------------------------------------

#[test]
fn vec_push_increments_len() {
    // Simplest possible push test - no drop body, no get.
    crate::assert_interpret_only!(
        {
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
            }

            class Main {
                fn main(given self) -> () {
                    let v: given Vec[Int] = new Vec[Int](array_new[Int](4), 0);
                    v.mut.push[mut[v]](42);
                    print(v.len.give);
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let v : given Vec[Int] = new Vec [Int] (array_new [Int](4), 0) ;
            Output: Trace:   v = Vec { data: Array { flag: Given, rc: 1, ⚡, ⚡, ⚡, ⚡ }, len: 0 }
            Output: Trace:   v . mut . push [mut [v]] (42) ;
            Output: Trace:   enter Vec.push
            Output: Trace:     array_write [Int, mut [self . data]](self . data . mut , self . len . give , value . give) ;
            Output: Trace:     self . len = self . len . give + 1 ;
            Output: Trace:     self . len = 1
            Output: Trace:     () ;
            Output: Trace:   exit Vec.push => ()
            Output: Trace:   print(v . len . give) ;
            Output: ----->   1
            Output: Trace:   () ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

// ---------------------------------------------------------------
// Vec push + get with P=given (move semantics)
// ---------------------------------------------------------------

#[test]
fn vec_push_and_get_given() {
    // Push 3 elements, then get element at index 1 with P=given.
    // When P=given, get() moves self.data out, drops elements 0 and 2,
    // and returns element 1. Vec drop body does NOT run (self partially moved).
    crate::assert_interpret_only!(
        {
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

                fn get[perm P](P self, index: Int) -> given_from[self] T {
                    let data: given_from[self.data] Array[T] = self.data.give;
                    let len: Int = self.len.give;
                    array_drop[T, given_from[self], ref[data]](data.ref, 0, index.give);
                    array_drop[T, given_from[self], ref[data]](data.ref, index.give + 1, len.give);
                    array_give[T, given_from[self], ref[data]](data.ref, index.give);
                }

                drop {
                    if is_last_ref[ref[self.data]](self.data.ref) {
                        array_drop[T, given, ref[self.data]](self.data.ref, 0, self.len.give);
                    } else {
                        ();
                    };
                }
            }

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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let v : given Vec[Data] = new Vec [Data] (array_new [Data](4), 0) ;
            Output: Trace:   v = Vec { data: Array { flag: Given, rc: 1, Data { value: ⚡ }, Data { value: ⚡ }, Data { value: ⚡ }, Data { value: ⚡ } }, len: 0 }
            Output: Trace:   v . mut . push [mut [v]] (new Data (10)) ;
            Output: Trace:   enter Vec.push
            Output: Trace:     array_write [Data, mut [self . data]](self . data . mut , self . len . give , value . give) ;
            Output: Trace:     self . len = self . len . give + 1 ;
            Output: Trace:     self . len = 1
            Output: Trace:     () ;
            Output: Trace:   exit Vec.push => ()
            Output: Trace:   v . mut . push [mut [v]] (new Data (20)) ;
            Output: Trace:   enter Vec.push
            Output: Trace:     array_write [Data, mut [self . data]](self . data . mut , self . len . give , value . give) ;
            Output: Trace:     self . len = self . len . give + 1 ;
            Output: Trace:     self . len = 2
            Output: Trace:     () ;
            Output: Trace:   exit Vec.push => ()
            Output: Trace:   v . mut . push [mut [v]] (new Data (30)) ;
            Output: Trace:   enter Vec.push
            Output: Trace:     array_write [Data, mut [self . data]](self . data . mut , self . len . give , value . give) ;
            Output: Trace:     self . len = self . len . give + 1 ;
            Output: Trace:     self . len = 3
            Output: Trace:     () ;
            Output: Trace:   exit Vec.push => ()
            Output: Trace:   let got : given Data = v . give . get [given] (1) ;
            Output: Trace:   enter Vec.get
            Output: Trace:     let data : given_from [self . data] Array[Data] = self . data . give ;
            Output: Trace:     data = Array { flag: Given, rc: 1, Data { value: 10 }, Data { value: 20 }, Data { value: 30 }, Data { value: ⚡ } }
            Output: Trace:     let len : Int = self . len . give ;
            Output: Trace:     len = 3
            Output: Trace:     array_drop [Data, given_from [self], ref [data]](data . ref , 0 , index . give) ;
            Output: Trace:     drop Data
            Output: Trace:       print(self . value . give) ;
            Output: ----->       10
            Output: Trace:     array_drop [Data, given_from [self], ref [data]](data . ref , index . give + 1 , len . give) ;
            Output: Trace:     drop Data
            Output: Trace:       print(self . value . give) ;
            Output: ----->       30
            Output: Trace:     array_give [Data, given_from [self], ref [data]](data . ref , index . give) ;
            Output: Trace:   exit Vec.get => given_from [self] Data { value: 20 }
            Output: Trace:   got = given_from [self] Data { value: 20 }
            Output: Trace:   print(got . value . give) ;
            Output: ----->   20
            Output: Trace:   () ;
            Output: Trace:   drop Data
            Output: Trace:     print(self . value . give) ;
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
    // Create a Vec, push elements, let it go out of scope.
    // The drop body should run, is_last_ref returns true (sole owner),
    // and all elements are dropped.
    crate::assert_interpret_only!(
        {
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

                drop {
                    if is_last_ref[ref[self.data]](self.data.ref) {
                        array_drop[T, given, ref[self.data]](self.data.ref, 0, self.len.give);
                    } else {
                        ();
                    };
                }
            }

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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let v : given Vec[Item] = new Vec [Item] (array_new [Item](4), 0) ;
            Output: Trace:   v = Vec { data: Array { flag: Given, rc: 1, Item { val: ⚡ }, Item { val: ⚡ }, Item { val: ⚡ }, Item { val: ⚡ } }, len: 0 }
            Output: Trace:   v . mut . push [mut [v]] (new Item (100)) ;
            Output: Trace:   enter Vec.push
            Output: Trace:     array_write [Item, mut [self . data]](self . data . mut , self . len . give , value . give) ;
            Output: Trace:     self . len = self . len . give + 1 ;
            Output: Trace:     self . len = 1
            Output: Trace:     () ;
            Output: Trace:   exit Vec.push => ()
            Output: Trace:   v . mut . push [mut [v]] (new Item (200)) ;
            Output: Trace:   enter Vec.push
            Output: Trace:     array_write [Item, mut [self . data]](self . data . mut , self . len . give , value . give) ;
            Output: Trace:     self . len = self . len . give + 1 ;
            Output: Trace:     self . len = 2
            Output: Trace:     () ;
            Output: Trace:   exit Vec.push => ()
            Output: Trace:   v . mut . push [mut [v]] (new Item (300)) ;
            Output: Trace:   enter Vec.push
            Output: Trace:     array_write [Item, mut [self . data]](self . data . mut , self . len . give , value . give) ;
            Output: Trace:     self . len = self . len . give + 1 ;
            Output: Trace:     self . len = 3
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
            Result: Ok: ()"#]]
    );
}

// ---------------------------------------------------------------
// Vec iter and next (given permission, consuming)
// ---------------------------------------------------------------

#[test]
fn vec_iter_and_next() {
    // Create a Vec, get a consuming Iterator (P=given), call next() once.
    // When iterator drops, remaining elements (indices 1,2) are cleaned up
    // via array_drop in Iterator.drop.
    crate::assert_interpret_only!(
        {
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

            class Iterator[perm P, ty T] {
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
                    let data: given_from[self.vec.data] Array[T] = self.vec.data.give;
                    let start: Int = self.start.give;
                    let len: Int = self.vec.len.give;
                    array_drop[T, P, ref[data]](data.ref, start.give, len.give);
                }
            }

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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let v : given Vec[Item] = new Vec [Item] (array_new [Item](4), 0) ;
            Output: Trace:   v = Vec { data: Array { flag: Given, rc: 1, Item { val: ⚡ }, Item { val: ⚡ }, Item { val: ⚡ }, Item { val: ⚡ } }, len: 0 }
            Output: Trace:   v . mut . push [mut [v]] (new Item (10)) ;
            Output: Trace:   enter Vec.push
            Output: Trace:     array_write [Item, mut [self . data]](self . data . mut , self . len . give , value . give) ;
            Output: Trace:     self . len = self . len . give + 1 ;
            Output: Trace:     self . len = 1
            Output: Trace:     () ;
            Output: Trace:   exit Vec.push => ()
            Output: Trace:   v . mut . push [mut [v]] (new Item (20)) ;
            Output: Trace:   enter Vec.push
            Output: Trace:     array_write [Item, mut [self . data]](self . data . mut , self . len . give , value . give) ;
            Output: Trace:     self . len = self . len . give + 1 ;
            Output: Trace:     self . len = 2
            Output: Trace:     () ;
            Output: Trace:   exit Vec.push => ()
            Output: Trace:   v . mut . push [mut [v]] (new Item (30)) ;
            Output: Trace:   enter Vec.push
            Output: Trace:     array_write [Item, mut [self . data]](self . data . mut , self . len . give , value . give) ;
            Output: Trace:     self . len = self . len . give + 1 ;
            Output: Trace:     self . len = 3
            Output: Trace:     () ;
            Output: Trace:   exit Vec.push => ()
            Output: Trace:   let it : Iterator[given, Item] = v . give . iter [given] () ;
            Output: Trace:   enter Vec.iter
            Output: Trace:     new Iterator [given, Item] (self . give, 0) ;
            Output: Trace:   exit Vec.iter => Iterator { vec: Vec { data: Array { flag: Given, rc: 1, Item { val: 10 }, Item { val: 20 }, Item { val: 30 }, Item { val: ⚡ } }, len: 3 }, start: 0 }
            Output: Trace:   it = Iterator { vec: Vec { data: Array { flag: Given, rc: 1, Item { val: 10 }, Item { val: 20 }, Item { val: 30 }, Item { val: ⚡ } }, len: 3 }, start: 0 }
            Output: Trace:   let first : given Item = it . mut . next [mut [it]] () ;
            Output: Trace:   enter Iterator.next
            Output: Trace:     let index : Int = self . start . give ;
            Output: Trace:     index = 0
            Output: Trace:     self . start = self . start . give + 1 ;
            Output: Trace:     self . start = 1
            Output: Trace:     array_give [Item, given, ref [self . vec . data]](self . vec . data . ref , index . give) ;
            Output: Trace:   exit Iterator.next => Item { val: 10 }
            Output: Trace:   first = Item { val: 10 }
            Output: Trace:   print(first . val . give) ;
            Output: ----->   10
            Output: Trace:   () ;
            Output: Trace:   drop Item
            Output: Trace:     print(self . val . give) ;
            Output: ----->     10
            Output: Trace:   drop Iterator
            Output: Trace:     let data : given_from [self . vec . data] Array[Item] = self . vec . data . give ;
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
            Result: Ok: ()"#]]
    );
}

// ---------------------------------------------------------------
// Shared Vec get (P=shared, non-consuming)
// ---------------------------------------------------------------

#[test]
fn shared_vec_get() {
    // Share a Vec, then get an element with P=shared.
    // array_drop with shared P is a no-op, array_give with shared P copies.
    // The shared Vec remains usable — its drop body runs but is_last_ref
    // guards cleanup (only the final handle cleans up elements).
    crate::assert_interpret_only!(
        {
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

                fn get[perm P](P self, index: Int) -> given_from[self] T {
                    let data: given_from[self.data] Array[T] = self.data.give;
                    let len: Int = self.len.give;
                    array_drop[T, given_from[self], ref[data]](data.ref, 0, index.give);
                    array_drop[T, given_from[self], ref[data]](data.ref, index.give + 1, len.give);
                    array_give[T, given_from[self], ref[data]](data.ref, index.give);
                }

                drop {
                    if is_last_ref[ref[self.data]](self.data.ref) {
                        array_drop[T, given, ref[self.data]](self.data.ref, 0, self.len.give);
                    } else {
                        ();
                    };
                }
            }

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
                    print(got.value.give);
                    ();
                }
            }
        },
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let v : given Vec[Data] = new Vec [Data] (array_new [Data](4), 0) ;
            Output: Trace:   v = Vec { data: Array { flag: Given, rc: 1, Data { value: ⚡ }, Data { value: ⚡ }, Data { value: ⚡ }, Data { value: ⚡ } }, len: 0 }
            Output: Trace:   v . mut . push [mut [v]] (new Data (10)) ;
            Output: Trace:   enter Vec.push
            Output: Trace:     array_write [Data, mut [self . data]](self . data . mut , self . len . give , value . give) ;
            Output: Trace:     self . len = self . len . give + 1 ;
            Output: Trace:     self . len = 1
            Output: Trace:     () ;
            Output: Trace:   exit Vec.push => ()
            Output: Trace:   v . mut . push [mut [v]] (new Data (20)) ;
            Output: Trace:   enter Vec.push
            Output: Trace:     array_write [Data, mut [self . data]](self . data . mut , self . len . give , value . give) ;
            Output: Trace:     self . len = self . len . give + 1 ;
            Output: Trace:     self . len = 2
            Output: Trace:     () ;
            Output: Trace:   exit Vec.push => ()
            Output: Trace:   let sv : shared Vec[Data] = v . give . share ;
            Output: Trace:   sv = shared Vec { data: Array { flag: Shared, rc: 1, Data { value: 10 }, Data { value: 20 }, Data { value: ⚡ }, Data { value: ⚡ } }, len: 2 }
            Output: Trace:   let got : shared Data = sv . give . get [shared] (0) ;
            Output: Trace:   enter Vec.get
            Output: Trace:     let data : given_from [self . data] Array[Data] = self . data . give ;
            Output: Trace:     data = shared Array { flag: Shared, rc: 3, Data { value: 10 }, Data { value: 20 }, Data { value: ⚡ }, Data { value: ⚡ } }
            Output: Trace:     let len : Int = self . len . give ;
            Output: Trace:     len = 2
            Output: Trace:     array_drop [Data, given_from [self], ref [data]](data . ref , 0 , index . give) ;
            Output: Trace:     array_drop [Data, given_from [self], ref [data]](data . ref , index . give + 1 , len . give) ;
            Output: Trace:     array_give [Data, given_from [self], ref [data]](data . ref , index . give) ;
            Output: Trace:     drop Vec
            Output: Trace:       if is_last_ref [ref [self . data]](self . data . ref) { array_drop [Data, given, ref [self . data]](self . data . ref , 0 , self . len . give) ; } else { () ; } ;
            Output: Trace:       () ;
            Output: Trace:   exit Vec.get => given_from [self] Data { value: 10 }
            Output: Trace:   got = given_from [self] Data { value: 10 }
            Output: Trace:   print(got . value . give) ;
            Output: ----->   10
            Output: Trace:   () ;
            Output: Trace:   drop Vec
            Output: Trace:     if is_last_ref [ref [self . data]](self . data . ref) { array_drop [Data, given, ref [self . data]](self . data . ref , 0 , self . len . give) ; } else { () ; } ;
            Output: Trace:     array_drop [Data, given, ref [self . data]](self . data . ref , 0 , self . len . give) ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

// ---------------------------------------------------------------
// Ref Vec get (P=ref, borrowing)
// ---------------------------------------------------------------

#[test]
fn ref_vec_get() {
    // Get an element through a ref to the Vec (P=ref[v]).
    // The element is a borrow — the Vec remains fully intact.
    crate::assert_interpret_only!(
        {
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

                fn get[perm P](P self, index: Int) -> given_from[self] T {
                    let data: given_from[self.data] Array[T] = self.data.give;
                    let len: Int = self.len.give;
                    array_drop[T, given_from[self], ref[data]](data.ref, 0, index.give);
                    array_drop[T, given_from[self], ref[data]](data.ref, index.give + 1, len.give);
                    array_give[T, given_from[self], ref[data]](data.ref, index.give);
                }

                drop {
                    if is_last_ref[ref[self.data]](self.data.ref) {
                        array_drop[T, given, ref[self.data]](self.data.ref, 0, self.len.give);
                    } else {
                        ();
                    };
                }
            }

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
        expect_test::expect![[r#"
            Output: Trace: enter Main.main
            Output: Trace:   let v : given Vec[Data] = new Vec [Data] (array_new [Data](4), 0) ;
            Output: Trace:   v = Vec { data: Array { flag: Given, rc: 1, Data { value: ⚡ }, Data { value: ⚡ }, Data { value: ⚡ }, Data { value: ⚡ } }, len: 0 }
            Output: Trace:   v . mut . push [mut [v]] (new Data (10)) ;
            Output: Trace:   enter Vec.push
            Output: Trace:     array_write [Data, mut [self . data]](self . data . mut , self . len . give , value . give) ;
            Output: Trace:     self . len = self . len . give + 1 ;
            Output: Trace:     self . len = 1
            Output: Trace:     () ;
            Output: Trace:   exit Vec.push => ()
            Output: Trace:   v . mut . push [mut [v]] (new Data (20)) ;
            Output: Trace:   enter Vec.push
            Output: Trace:     array_write [Data, mut [self . data]](self . data . mut , self . len . give , value . give) ;
            Output: Trace:     self . len = self . len . give + 1 ;
            Output: Trace:     self . len = 2
            Output: Trace:     () ;
            Output: Trace:   exit Vec.push => ()
            Output: Trace:   let got : ref [v] Data = v . ref . get [ref [v]] (1) ;
            Output: Trace:   enter Vec.get
            Output: Trace:     let data : given_from [self . data] Array[Data] = self . data . give ;
            Output: Trace:     data = ref [v] Array { flag: Borrowed, rc: 1, Data { value: 10 }, Data { value: 20 }, Data { value: ⚡ }, Data { value: ⚡ } }
            Output: Trace:     let len : Int = self . len . give ;
            Output: Trace:     len = 2
            Output: Trace:     array_drop [Data, given_from [self], ref [data]](data . ref , 0 , index . give) ;
            Output: Trace:     array_drop [Data, given_from [self], ref [data]](data . ref , index . give + 1 , len . give) ;
            Output: Trace:     array_give [Data, given_from [self], ref [data]](data . ref , index . give) ;
            Output: Trace:   exit Vec.get => given_from [self] Data { value: 20 }
            Output: Trace:   got = given_from [self] Data { value: 20 }
            Output: Trace:   print(got . value . give) ;
            Output: ----->   20
            Output: Trace:   () ;
            Output: Trace:   drop Vec
            Output: Trace:     if is_last_ref [ref [self . data]](self . data . ref) { array_drop [Data, given, ref [self . data]](self . data . ref , 0 , self . len . give) ; } else { () ; } ;
            Output: Trace:     array_drop [Data, given, ref [self . data]](self . data . ref , 0 , self . len . give) ;
            Output: Trace: exit Main.main => ()
            Result: Ok: ()"#]]
    );
}

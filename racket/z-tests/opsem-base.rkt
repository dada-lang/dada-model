#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require "../dada.rkt")

(; Just before we pop the sequence, we have a stack segment with the two variables.
 dada-seq-test
 [(var my-var = 22) (var another-var = 44)]
 [(my-var (our box Heap-addr)) (another-var (our box Heap-addr1))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 44))]
 []
 the-Zero-value)

(; After giving `(another-var)`, its value becomes expired
 dada-seq-test
 ((var my-var = 22) (var another-var = 44) (give (another-var)))
 [(my-var (our box Heap-addr)) (another-var expired)]
 [(Heap-addr (box 1 22)) (Heap-addr1 (box 1 44))]
 []
 (our box Heap-addr1))

(; After copying `(another-var)`, its value remains
 dada-seq-test
 ((var my-var = 22) (var another-var = 44) (copy (another-var)))
 [(my-var (our box Heap-addr)) (another-var (our box Heap-addr1))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 2 44))]
 []
 (our box Heap-addr1))

(; Test upcast
 dada-seq-test
 ((var my-var = 22) (var another-var = (44 : int)) (copy (another-var)))
 [(my-var (our box Heap-addr)) (another-var (our box Heap-addr1))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 2 44))]
 []
 (our box Heap-addr1))

(; Test creating a class instance and freezing it.
 ; The ref count winds up as 2.
 dada-seq-test
 ((var my-var = 22)
  (var point = (freeze (class-instance Point () (22 33))))
  (copy (point))
  )
 [(my-var (our box Heap-addr)) (point (our box Heap-addr3))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 22))
  (Heap-addr2 (box 1 33))
  (Heap-addr3 (box 2 ((class Point) ((x (our box Heap-addr1)) (y (our box Heap-addr2))))))]
 []
 (our box Heap-addr3))

(; Test creating a data instance and giving it.
 ; The ref count winds up as 1.
 dada-seq-test
 ((var my-var = 22)
  (var point = (class-instance Point () (22 33)))
  (give (point))
  )
 [(my-var (our box Heap-addr)) (point expired)]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 22))
  (Heap-addr2 (box 1 33))
  (Heap-addr3 (box 1 ((class Point) ((x (our box Heap-addr1)) (y (our box Heap-addr2))))))]
 []
 (my box Heap-addr3))

(; Test creating a data instance and dropping it.
 ; The heap address is released.
 dada-seq-test
 ((var my-var = 22)
  (var point = (class-instance Point () (22 33)))
  (give (point))
  (copy (my-var)))
 [(my-var (our box Heap-addr)) (point expired)]
 [(Heap-addr (box 2 22))]
 []
 (our box Heap-addr))

(; Test creating a class instance that stores a frozen of another instance.
 ; The ref count is properly adjusted.
 dada-seq-test
 ((var point = (freeze (class-instance Point () (22 33))))
  (var vec = (class-instance Vec [(my Point ())] ((copy (point)))))
  )
 [(point (our box Heap-addr2))
  (vec (my box Heap-addr3))
  ]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 33))
  (Heap-addr2 (box 2 ((class Point) ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
  (Heap-addr3 (box 1 ((class Vec) ((value0 (our box Heap-addr2))))))
  ]
 []
 the-Zero-value)

(; Test asserting the type of something.
 dada-seq-test
 [(var point = (class-instance Point () (22 33)))
  (assert-ty (point) : (my Point ()))]
 [(point (my box Heap-addr2))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 33))
  (Heap-addr2 (box 1 ((class Point) ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
  ]
 []
 the-Zero-value)

(; Test setting values.
 ;
 ; Note that the old value (Heap-addr) is dropped.
 dada-seq-test
 [(var point = (class-instance Point () (22 33)))
  (set (point) = (class-instance Point () (44 66)))]
 [(point (my box Heap-addr5))]
 [(Heap-addr3 (box 1 44))
  (Heap-addr4 (box 1 66))
  (Heap-addr5 (box 1 ((class Point) ((x (our box Heap-addr3)) (y (our box Heap-addr4))))))
  ]
 []
 the-Zero-value)

(; Test setting values to themselves.
 ;
 ; Here, the `give (point)` overwrites `point` (temporarily) with `expired`,
 ; so that when we drop the existing value, that's a no-op. Then we write the old
 ; value back into it.
 dada-seq-test
 [(var point = (class-instance Point () (22 33)))
  (set (point) = (give (point)))]
 [(point (my box Heap-addr2))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 33))
  (Heap-addr2 (box 1 ((class Point) ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
  ]
 []
 the-Zero-value)

#;(; Test that copy data clones-- otherwise, `point2` would be pointing at freed memory.
   ;
   ; FIXME-- copying a `my` is no longer permitted! This would be a good "Goes wrong" test.
   dada-seq-test
   ((var point1 = (class-instance Point () (22 33)))
    (var point2 = (copy (point1)))
    (set (point1) = (class-instance Point () (44 66)))
    (copy (point2 x))
    )
   [(point1 (my box Heap-addr1))
    (point2 (my box Heap-addr))
    ]
   [(Heap-addr (box 1 ((class Point) ((x 22) (y 33)))))
    (Heap-addr1 (box 1 ((class Point) ((x 44) (y 66)))))
    ]
   []
   22)

(; Use freeze to increment ref count-- otherwise, `point2` would be pointing at freed memory.
 dada-seq-test
 ((var point1 = (freeze (class-instance Point () (22 33))))
  (var point2 = (copy (point1)))
  (set (point1) = (class-instance Point () (44 66)))
  (copy (point2 x))
  )
 [(point1 (my box Heap-addr5))
  (point2 (our box Heap-addr2))
  ]
 [(Heap-addr (box 2 22))
  (Heap-addr1 (box 1 33))
  (Heap-addr2 (box 1 ((class Point) ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
  (Heap-addr3 (box 1 44))
  (Heap-addr4 (box 1 66))
  (Heap-addr5 (box 1 ((class Point) ((x (our box Heap-addr3)) (y (our box Heap-addr4))))))
  ]
 []
 (our box Heap-addr))

(; Test setting the value of a class instance that has data type
 dada-seq-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (set (vec1 value0) = 44))
 [(vec1 (my box Heap-addr1))]
 [(Heap-addr1 (box 1 ((class Vec) ((value0 (our box Heap-addr2))))))
  (Heap-addr2 (box 1 44))]
 []
 the-Zero-value)

(; Test borrowing a vector and mutating the field through the borrow.
 dada-seq-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (var vec2 = (lend (vec1)))
  (set (vec2 value0) = 44))
 [(vec1 (my box Heap-addr1))
  (vec2 ((lent Lease-id) box Heap-addr1))
  ]
 [(Heap-addr1 (box 1 ((class Vec) ((value0 (our box Heap-addr2))))))
  (Heap-addr2 (box 1 44))]
 [(Lease-id (lent () Heap-addr1))]
 the-Zero-value)

(; Test subleasing
 dada-seq-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (var vec2 = (lend (vec1)))
  (var vec3 = (lend (vec2)))
  (set (vec3 value0) = 44))
 [(vec1 (my box Heap-addr1))
  (vec2 ((lent Lease-id) box Heap-addr1))
  (vec3 ((lent Lease-id1) box Heap-addr1))
  ]
 [(Heap-addr1 (box 1 ((class Vec) ((value0 (our box Heap-addr2))))))
  (Heap-addr2 (box 1 44))]
 [(Lease-id (lent () Heap-addr1))
  (Lease-id1 (lent (Lease-id) Heap-addr1))]
 the-Zero-value)

(; Test that values introduced within a seq get dropped,
 ; except the result of the sequence.
 dada-full-test
 ((var point1 = (freeze (class-instance Point () (22 33))))
  (var point2 = (copy (point1)))
  (set (point1) = (class-instance Point () (44 66)))
  (copy (point2 x))
  )
 [(Heap-addr (box 1 22))]
 []
 (our box Heap-addr))

#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         "../dada.rkt")

(; Just before we pop the sequence, we have a stack segment with the two variables.
 dada-seq-test [(var my-var = 22) (var another-var = 44)]
               [(my-var 22) (another-var 44)]
               []
               []
               0)

(; After giving `(another-var)`, its value becomes expired
 dada-seq-test
 ((var my-var = 22) (var another-var = 44) (give (another-var)))
 [(my-var 22) (another-var expired)]
 []
 []
 44)

(; After copying `(another-var)`, its value remains
 dada-seq-test
 ((var my-var = 22) (var another-var = 44) (copy (another-var)))
 [(my-var 22) (another-var 44)]
 []
 []
 44)

(; Test upcast
 dada-seq-test
 ((var my-var = 22) (var another-var = (44 : int)) (copy (another-var)))
 [(my-var 22) (another-var 44)]
 []
 []
 44)

(; Test creating a class instance and copying it.
 ; The ref count winds up as 2.
 dada-seq-test
 ((var my-var = 22)
  (var point = (class-instance Point () (22 33)))
  (copy (point))
  )
 [(my-var 22) (point (my box Heap-addr))]
 [(Heap-addr (box 2 ((class Point) ((x 22) (y 33)))))]
 []
 (my box Heap-addr))

(; Test creating a data instance and giving it.
 ; The ref count winds up as 1.
 dada-seq-test
 ((var my-var = 22)
  (var point = (class-instance Point () (22 33)))
  (give (point))
  )
 [(my-var 22) (point expired)]
 [(Heap-addr (box 1 ((class Point) ((x 22) (y 33)))))]
 []
 (my box Heap-addr))

(; Test creating a data instance and dropping it.
 ; The heap address is released.
 dada-seq-test
 ((var my-var = 22)
  (var point = (class-instance Point () (22 33)))
  (give (point))
  0)
 [(my-var 22) (point expired)]
 []
 []
 0)

(; Test creating a class instance that stores a copy of another instance.
 ; The ref count is properly adjusted.
 dada-seq-test
 ((var point = (class-instance Point () (22 33)))
  (var vec = (class-instance Vec [(my Point ())] ((copy (point)))))
  )
 [(point (my box Heap-addr))
  (vec (my box Heap-addr1))
  ]
 [(Heap-addr1 (box 1 ((class Vec) ((value0 (my box Heap-addr))))))
  (Heap-addr (box 2 ((class Point) ((x 22) (y 33)))))]
 []
 0)

(; Test asserting the type of something.
 dada-seq-test
 [(var point = (class-instance Point () (22 33)))
  (assert-ty (point) : (my Point ()))]
 [(point (my box Heap-addr))]
 [(Heap-addr (box 1 ((class Point) ((x 22) (y 33)))))]
 []
 0)

(; Test setting values.
 ;
 ; Note that the old value (Heap-addr) is dropped.
 dada-seq-test
 [(var point = (class-instance Point () (22 33)))
  (set (point) = (class-instance Point () (44 66)))]
 [(point (my box Heap-addr1))]
 [(Heap-addr1 (box 1 ((class Point) ((x 44) (y 66)))))]
 []
 0)

(; Test setting values to themselves.
 ;
 ; Here, the `give (point)` overwrites `point` (temporarily) with `expired`,
 ; so that when we drop the existing value, that's a no-op. Then we write the old
 ; value back into it.
 dada-seq-test
 [(var point = (class-instance Point () (22 33)))
  (set (point) = (give (point)))]
 [(point (my box Heap-addr))]
 [(Heap-addr (box 1 ((class Point) ((x 22) (y 33)))))]
 []
 0)

(; Test that copy data clones-- otherwise, `point2` would be pointing at freed memory.
 dada-seq-test
 ((var point1 = (class-instance Point () (22 33)))
  (var point2 = (copy (point1)))
  (set (point1) = (class-instance Point () (44 66)))
  (copy (point2 x))
  )
 [(point1 (my box Heap-addr1))
  (point2 (my box Heap-addr))
  ]
 [(Heap-addr1 (box 1 ((class Point) ((x 44) (y 66)))))
  (Heap-addr (box 1 ((class Point) ((x 22) (y 33)))))
  ]
 []
 22)

(; Test setting the value of a class instance that has data type
 dada-seq-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (set (vec1 value0) = 44))
 [(vec1 (my box Heap-addr))]
 [(Heap-addr (box 1 ((class Vec) ((value0 44)))))]
 []
 0)

(; Test borrowing a vector and mutating the field through the borrow.
 dada-seq-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (var vec2 = (lend (vec1)))
  (set (vec2 value0) = 44))
 [(vec1 (my box Heap-addr))
  (vec2 ((leased Lease-id) box Heap-addr))
  ]
 [(Heap-addr (box 1 ((class Vec) ((value0 44)))))]
 [(Lease-id (lent () Heap-addr))]
 0)

(; Test subleasing
 dada-seq-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (var vec2 = (lend (vec1)))
  (var vec3 = (lend (vec2)))
  (set (vec3 value0) = 44))
 [(vec1 (my box Heap-addr))
  (vec2 ((leased Lease-id) box Heap-addr))
  (vec3 ((leased Lease-id1) box Heap-addr))
  ]
 [(Heap-addr (box 1 ((class Vec) ((value0 44)))))]
 [(Lease-id (lent () Heap-addr))
  (Lease-id1 (lent (Lease-id) Heap-addr))]
 0)

(; Test that values introduced within a seq get dropped.
 dada-full-test
 ((var point1 = (class-instance Point () (22 33)))
  (var point2 = (copy (point1)))
  (set (point1) = (class-instance Point () (44 66)))
  (copy (point2 x))
  )
 []
 []
 22)

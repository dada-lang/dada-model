#lang racket

(require redex
         "../dada.rkt")

(; NB: Reading `point x` expires both `lent-point` and `shared-point2`
 dada-seq-test
 [(var point = (class-instance Point () (22 44)))
  (var lent-point = (lend (point)))
  (var some = (class-instance Some
                              (((lent ((lent (point)))) Point ()))
                              ((give (lent-point)))))
  (var shared-some = (share (some)))
  (var shared-point2 = (copy (shared-some value)))
  (copy (point x))
  ]
 [(point (my box Heap-addr2))
  (lent-point expired)
  (some (my box Heap-addr3))
  (shared-some ((shared Lease-id1) box Heap-addr3))
  (shared-point2 expired)
  ]
 [(Heap-addr (box 2 22))
  (Heap-addr1 (box 1 44))
  (Heap-addr2 (box 1 ((class Point) ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
  (Heap-addr3 (box 1 ((class Some) ((value expired)))))
  ]
 [(Lease-id1 (shared () Heap-addr3))
  ]
 (our box Heap-addr))

(; Test subleasing and sharing
 ;
 ; FIXME: It's a bit debatable, but this setup won't
 ; match the static type system, at least-- the second share
 ; is derived from the first one, so when the first one
 ; gets canceled, shouldn't the second one? On the other hand,
 ; even if share is actually an owner, there isn't really
 ; a *need* to cancel the second one, but I suspect we will
 ; have to in order to make everything work.
 dada-seq-test
 ((var point1 = (class-instance Point () (22 44)))
  (var point2 = (class-instance Point () (66 88)))
  (var pair = (class-instance Pair
                              ((my Point ())
                               (my Point ()))
                              ((give (point1))
                               (give (point2)))))
  (var p = (share (pair)))
  (var q = (share (pair a)))
  (set (pair b y) = 99)
  )
 ((point1 expired)
  (point2 expired)
  (pair (my box Heap-addr6))
  (p expired)
  (q ((shared Lease-id1) box Heap-addr2))
  )
 ((Heap-addr (box 1 22))
  (Heap-addr1 (box 1 44))
  (Heap-addr2
   (box
    1
    ((class Point) ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
  (Heap-addr3 (box 1 66))
  (Heap-addr5
   (box
    1
    ((class Point) ((x (our box Heap-addr3)) (y (our box Heap-addr7))))))
  (Heap-addr6
   (box 1 ((class Pair) ((a (my box Heap-addr2)) (b (my box Heap-addr5))))))
  (Heap-addr7 (box 1 99)))
 ((Lease-id1 (shared () Heap-addr2)))
 the-Zero-value)
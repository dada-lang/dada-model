#lang racket

(require "../dada.rkt")

(; Freezing and then moving is a copy.
 dada-seq-test
 ((var p = (class-instance Point () (22 44)))
  (var p1 = (freeze (p)))
  (var q = (move (p)))
  )
 [(p (our box Heap-addr))
  (p1 (our box Heap-addr))
  (q (our box Heap-addr))]
 [(Heap-addr (box 3 ((class Point) ((x 22) (y 44)))))]
 []
 the-Zero-value)

(; Freezing and then moving is a copy.
 ;
 ; FIXME-- read-value doesn't realize the `my Point` in the vec
 ; was reached through an `our` ref
 dada-seq-test
 ((var p1 = (class-instance Point () (22 44)))
  (var v1 = (class-instance Vec ((my Point ())) ((move (p1)))))
  (var v2 = (freeze (v1)))
  (var p2 = (move (v1 value0)))
  )
 [(p1 expired)
  (v1 (our box Heap-addr1))
  (v2 (our box Heap-addr1))
  (p2 (my box Heap-addr))]
 [(Heap-addr (box 1 ((class Point) ((x 22) (y 44)))))
  (Heap-addr1 (box 2 ((class Vec) ((value0 expired)))))
  ]
 []
 the-Zero-value)


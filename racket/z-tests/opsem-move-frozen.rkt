#lang racket

(require "../dada.rkt")

(; Freezing and then moving is a copy.
 dada-seq-test
 ((var p = (class-instance Point () (22 44)))
  (var p1 = (freeze (p)))
  (var q = (move (p)))
  )
 [(p (our box Heap-addr2))
  (p1 (our box Heap-addr2))
  (q (our box Heap-addr2))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 44))
  (Heap-addr2 (box 3 ((class Point) ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
  ]
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
  (v1 (our box Heap-addr3))
  (v2 (our box Heap-addr3))
  (p2 (my box Heap-addr2))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 44))
  (Heap-addr2 (box 1 ((class Point) ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
  (Heap-addr3 (box 2 ((class Vec) ((value0 expired)))))]
 []
 the-Zero-value)


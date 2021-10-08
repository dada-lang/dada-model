#lang racket
(require redex)
(require "dada.rkt")

(; Freezing and then moving is a copy.
 dada-trace-test
 ((var p1 = (class-instance Point () (22 44)))
  (var v1 = (class-instance Vec ((my Point ())) ((move (p1)))))
  (var v2 = (freeze (v1)))
  (var p2 = (move (v1 value0)))
  )
 [(p1 expired)
  (v1 (our box Heap-addr1))
  (v2 (our box Heap-addr1))
  (p2 (my box Heap-addr))]
 [(Heap-addr1 (box 2 ((class Vec) ((value0 (my box Heap-addr))))))
  (Heap-addr (box 1 ((class Point) ((x 22) (y 44)))))
  ]
 []
 0)
#lang racket

(require "../dada.rkt")

(; Sharing and then moving is a copy.
 dada-seq-test
 ((var p = (share (class-instance Point () (22 44))))
  (var q = (give (p)))
  )
 [(p (our box Heap-addr2))
  (q (our box Heap-addr2))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 44))
  (Heap-addr2 (box 2 ((class Point) ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
  ]
 []
 the-Zero-value)

(; Sharing and then moving is a copy.
 dada-seq-test
 ((var p1 = (class-instance Point () (22 44)))
  (var v1 = (share (class-instance Vec ((my Point ())) ((give (p1))))))
  (var p2 = (give (v1 value0)))
  )
 [(p1 expired)
  (v1 (our box Heap-addr3))
  (p2 (our box Heap-addr2))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 44))
  (Heap-addr2 (box 2 ((class Point) ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
  (Heap-addr3 (box 1 ((class Vec) ((value0 (my box Heap-addr2))))))]
 []
 the-Zero-value)


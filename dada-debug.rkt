#lang racket
(require redex/reduction-semantics
         "racket/dada.rkt"
         "racket/util.rkt"
         "racket/opsem/traverse.rkt")

(current-traced-metafunctions '(move-place access-permissions))

(; Sharing and then moving is a copy.
 ;
 ; FIXME-- read-value doesn't realize the `my Point` in the vec
 ; was reached through an `our` ref
 dada-seq-test
 ((var p1 = (class-instance Point () (22 44)))
  (var v1 = (share (class-instance Vec ((my Point ())) ((move (p1))))))
  (var p2 = (move (v1 value0)))
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
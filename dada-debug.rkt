#lang racket
(require redex/reduction-semantics)
(require "racket/dada.rkt")

(current-traced-metafunctions '())

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
#lang racket
(require redex)
(require "dada.rkt")

(; Test lease cancellation
dada-seq-test
((var vec1 = (class-instance Vec (int) (22)))
  (var vec2 = (lend (vec1)))
  (var vec3 = (lend (vec1)))
  (set (vec3 value0) = 44))
 [(vec1 (my box Heap-addr))
  (vec2 expired)
  (vec3 ((leased Lease-id1) box Heap-addr))
  ]
 [(Heap-addr (box 1 ((class Vec) ((value0 44)))))]
 [(Lease-id1 (borrowed () Heap-addr))]
 0)
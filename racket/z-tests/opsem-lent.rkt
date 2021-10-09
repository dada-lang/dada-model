#lang racket

(require redex
         "../dada.rkt")

(; NB: Reading `point x` expires both `lent-point` and `shared-point2`
 dada-seq-test
 [(var point = (class-instance Point () (22 44)))
  (var lent-point = (seq ((var t = (lend (point)))
                          (lend (t))
                          )))
  (set (lent-point x) = 66)
  ]
 [(point (my box Heap-addr2))
  (lent-point ((lent Lease-id1) box Heap-addr2))
  ]
 [(Heap-addr1 (box 1 44))
  (Heap-addr2 (box 1 ((class Point) ((x (our box Heap-addr3)) (y (our box Heap-addr1))))))
  (Heap-addr3 (box 1 66))
  ]
 [(Lease-id (lent () Heap-addr2))
  (Lease-id1 (lent (Lease-id) Heap-addr2))
  ]
 the-Zero-value)
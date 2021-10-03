#lang racket
(require redex)
(require "dada.rkt")

(; Moving a (lent String) value contained within a
 ; p: (lent Some<my Point>) subleases the two lent variables.
 dada-seq-test
 ((var point = (class-instance Point () (22 44)))
  (var lent-point = (lend (point)))
  (var some-lent-point = (class-instance Some (((lent ((lent (point)))) Point ())) ((give (lent-point)))))
  (var p = (lend (some-lent-point)))
  (var r = (move (p value)))
  )
 [(point (my box Heap-addr))
  (lent-point expired)
  (some-lent-point (my box Heap-addr1))
  (p ((leased Lease-id1) box Heap-addr1))
  (r ((leased Lease-id2) box Heap-addr))]
 [(Heap-addr1 (box 1 ((class Some) ((value ((leased Lease-id) box Heap-addr))))))
  (Heap-addr (box 1 ((class Point) ((x 22) (y 44)))))
  ]
 [(Lease-id (lent () Heap-addr))
  (Lease-id1 (lent () Heap-addr1))
  (Lease-id2 (lent (Lease-id1 Lease-id) Heap-addr))]
 0)
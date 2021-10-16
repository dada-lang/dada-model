#lang racket
(require redex/reduction-semantics
         "racket/dada.rkt"
         "racket/util.rkt"
         "racket/opsem/traverse.rkt")

(current-traced-metafunctions '())

(; Sharing a lent value inside of an our => shared value
 dada-seq-test
 [(var pair = (class-instance Pair
                              ()
                              ((class-instance String () ())
                               44)))
  (var some = (class-instance Some
                              ()
                              ((lend (pair)))))
  (var a = (share (some)))
  (var b = (share (a value a)))
  ]
 [(pair (my box Heap-addr2))
  (some (my box Heap-addr3))
  (a ((shared Lease-id1) box Heap-addr3))
  (b ((shared Lease-id2) box Heap-addr))]
 [(Heap-addr (box 1 ((class String) ())))
  (Heap-addr1 (box 1 44))
  (Heap-addr2
   (box 1 ((class Pair) ((a (my box Heap-addr)) (b (our box Heap-addr1))))))
  (Heap-addr3 (box 1 ((class Some) ((value ((lent Lease-id) box Heap-addr2))))))]
 [(Lease-id (lent () Heap-addr2))
  (Lease-id1 (shared () Heap-addr3))
  (Lease-id2 (shared (Lease-id Lease-id1) Heap-addr))]
 (our box the-Zero))
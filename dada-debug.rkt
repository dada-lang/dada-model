#lang racket
(require redex/reduction-semantics
         "racket/dada.rkt"
         "racket/util.rkt"
         "racket/opsem/traverse.rkt")

(current-traced-metafunctions '())

(; Test that we are able to move both a/b from a lent origin,
 ; just as if we owned it (in which case those fields would be nulled out).
 dada-seq-test
 ((var pair-some = (class-instance Pair () ((class-instance Some () (22))
                                            (class-instance Some () (44)))))
  (var lent-pair = (lend (pair-some)))
  (var lent-a = (give (lent-pair a)))
  (var lent-b = (give (lent-pair b)))
  )
 [(pair-some (my box Heap-addr4))
  (lent-pair ((lent Lease-id) box Heap-addr4))
  (lent-a ((lent Lease-id1) box Heap-addr1))
  (lent-b ((lent Lease-id2) box Heap-addr3))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 ((class Some) ((value (our box Heap-addr))))))
  (Heap-addr2 (box 1 44))
  (Heap-addr3 (box 1 ((class Some) ((value (our box Heap-addr2))))))
  (Heap-addr4
   (box
    1
    ((class Pair)
     ((a (my box Heap-addr1))
      (b (my box Heap-addr3))))))]
 [(Lease-id (lent () Heap-addr4))
  (Lease-id1 (lent (Lease-id) Heap-addr1))
  (Lease-id2 (lent (Lease-id) Heap-addr3))]
 the-Zero-value)
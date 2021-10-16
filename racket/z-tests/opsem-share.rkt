#lang racket

(require redex
         "../dada.rkt")

(; Sharing an owned value => shared value
 dada-seq-test
 [(var a = (class-instance Some
                           ()
                           ((class-instance Pair
                                            ()
                                            ((class-instance String () ())
                                             44)))))
  (var b = (share (a value a)))
  ]
 [(a (my box Heap-addr3))
  (b ((shared Lease-id) box Heap-addr))]
 [(Heap-addr (box 1 ((class String) ())))
  (Heap-addr1 (box 1 44))
  (Heap-addr2
   (box 1 ((class Pair) ((a (my box Heap-addr)) (b (our box Heap-addr1))))))
  (Heap-addr3 (box 1 ((class Some) ((value (my box Heap-addr2))))))]
 [(Lease-id (shared () Heap-addr))]
 (our box the-Zero))

(; Sharing an integer in a var field gives me back a fresh ref
 dada-seq-test
 [(var a = (class-instance Some
                           ()
                           ((class-instance Pair
                                            ()
                                            ((class-instance String () ())
                                             44)))))
  (var b = (share (a value b)))
  ]
 [(a (my box Heap-addr3))
  (b (our box Heap-addr1))]
 [(Heap-addr (box 1 ((class String) ())))
  (Heap-addr1 (box 2 44))
  (Heap-addr2
   (box 1 ((class Pair) ((a (my box Heap-addr)) (b (our box Heap-addr1))))))
  (Heap-addr3 (box 1 ((class Some) ((value (my box Heap-addr2))))))]
 []
 (our box the-Zero))

(; Sharing an integer in an atomic field gives me back a fresh ref
 dada-seq-test
 [(var a = (class-instance Cell
                           ()
                           (22)))
  (var b = (share (a value)))
  ]
 [(a (my box Heap-addr1))
  (b (our box Heap-addr))]
 [
  (Heap-addr (box 2 22))
  (Heap-addr1 (box 1 ((class Cell) ((value (our box Heap-addr))))))]
 []
 (our box the-Zero))
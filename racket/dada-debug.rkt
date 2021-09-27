#lang racket
(require redex)
(require "dada.rkt")

#;(; Test sharing an our instance (equivalent to cloning).
 dada-trace-test
 ((var point = ((class-instance Point () (22 33)) : (our Point ())))
  (var spoint = (share (point))))
 [(point (my box Heap-addr))
  (spoint (my box Heap-addr))]
 [(Heap-addr (box 2 ((class Point) ((x 22) (y 33)))))]
 []
 0)
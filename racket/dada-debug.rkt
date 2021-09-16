#lang racket
(require redex)
(require "dada.rkt")

(; Test shared lease cancellation on drop
 dada-trace-test
 ((var sh1 = ((class-instance ShVar ((my Vec (int))) ((class-instance Vec (int) (22)))): (our ShVar ((my Vec (int))))))
  (var sh2 = (copy (sh1)))
  (atomic (seq ((var v1 = (lend (sh1 shv)))
                
                (set (v1 value0) = 44)
                (var v2 = (lend (sh2 shv)))
                (set (v2 value0) = 66)
                (set (v1 value0) = 88)
                ))))
 []
 []
 []
 0)
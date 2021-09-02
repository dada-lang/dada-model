#lang racket
(require redex)
(require "dada.rkt")

(redex-let*
 Dada
 [(program (term program_test))]
 (dada-check-fail
  program_test
  (seq ((var p = (data-instance Point () (10 20)))
        (seq ((var x = 22)
              (var y = 44)))
        (set (p) = (data-instance Point () ((copy (x)) (copy (y)))))))
  ))

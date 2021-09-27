#lang racket
(require redex)
(require "../dada.rkt")

(dada-check-fail
  program_test
  (seq ((var p = (class-instance Point () (10 20)))
        (seq ((var x = 22)
              (var y = 44)))
        (set (p) = (class-instance Point () ((copy (x)) (copy (y)))))))
  )

(dada-check-pass
  program_test
  (seq ((var p = ((class-instance Point () (10 20)) : (our Point ())))
        (seq ((var x = 22)
              (var y = 44)
              (set (p) = (class-instance Point () ((copy (x)) (copy (y)))))))
        (copy (p))))
  )

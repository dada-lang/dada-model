#lang racket
(require redex)
(require "../dada.rkt")

(dada-check-program-ok
 (test-program () ()))

(; fn identity(x: int) -> int { x.give }
 dada-check-program-ok
 (test-program
  ()
  ((hello-world (fn (() ((x int)) -> int) = (give (x)))))))
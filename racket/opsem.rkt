#lang racket
(require redex)
(require "grammar.rkt")
(provide (all-defined-out))

(define-extended-language DadaExec Dada
  (heap ()))
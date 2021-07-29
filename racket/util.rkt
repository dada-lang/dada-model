#lang racket
(require redex data/order)
(provide (all-defined-out))

(define-syntax-rule (test-equal-terms a b) (test-equal (term a) (term b)))

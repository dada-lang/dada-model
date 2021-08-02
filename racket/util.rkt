#lang racket
(require redex data/order)
(provide (all-defined-out))

(define-syntax-rule (test-equal-terms a b) (test-equal (term a) (term b)))
(define-syntax-rule (log name value) (begin (pretty-print '(entering name value)) (let [(v value)] (pretty-print (list 'exiting name v)) value)))
(define (partition-list f l) (let-values [((matches matches-not) (partition f l))] (list matches matches-not)))
(define-syntax-rule (test-judgment-false j) (test-equal (judgment-holds j) #f))
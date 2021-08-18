#lang racket
(require redex data/order)
(provide (all-defined-out))

(define-syntax-rule (test-equal-terms a b) (test-equal (term a) (term b)))
(define-syntax-rule (test-match-terms l a b) (test-match l b (term a)))
(define-syntax-rule (log name value) (begin (pretty-print (term ("entering" name))) (let [(v value)] (pretty-print (term ("exiting" name "with result" ,v))) v)))
(define (partition-list f l) (let-values [((matches matches-not) (partition f l))] (list matches matches-not)))
(define-syntax-rule (test-judgment-false j) (test-equal (judgment-holds j) #f))

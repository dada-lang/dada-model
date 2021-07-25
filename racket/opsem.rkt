#lang racket
(require redex)
(require "grammar.rkt")
(provide (all-defined-out))

;; Convention: uppercase names are things that only exist at runtime
(define-extended-language Dada dada
  (Program (program Stack Heap Ref-counts Expr))
  (Stack (stack Stack-value ...))
  (Stack-value (x Value))
  (Heap (heap Heap-value ...))
  (Heap-value (Address Value))
  (Ref-counts (ref-counts (Identity number) ...))
  (Value
   ;; class/struct instance
   (Identity ty (Field-value ...))

   ;; indirection to heap
   Address

   ;; numeric value, builtin for convenience
   number)
  (Field-value (field Value))
  (Expr (let var-decl = Expr)
        (let var-decl = Value)
        (set place = Expr)
        (set place = Value)
        ;; evaluate call arguments left to right
        (call f (Value ... Expr expr ...))
        (call f (Value ...))
        (access place)
        number
        ;; evaluate left to right
        (seq Expr expr ...)
        (seq Value expr ...)
        (dead x)
        hole)
  (Address variable-not-otherwise-mentioned)
  (Identity variable-not-otherwise-mentioned))

(define reductions
  (reduction-relation
   Dada
   (c--> (seq Value expr ...)
         ,(seq expr ...)
         "set-step")
   with
   [(--> (in-hole Program_1 a) (in-hole Program_1 b))
    (c--> a b)]))

(test-match Dada Program (term (program (stack) (heap) (ref-counts) 22)))
(test-match Dada Stack (term (stack)))
(test-match Dada Heap (term (heap)))
(test-match Dada Ref-counts (term (ref-counts)))
(test-match Dada Expr (term (seq 22 44 66)))
;(traces reductions
;        (term (program (stack) (heap) (ref-counts) (seq 22 44 66))))
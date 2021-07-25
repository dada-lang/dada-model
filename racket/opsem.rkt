#lang racket
(require redex)
(require "grammar.rkt")
(provide (all-defined-out))

;; Convention: uppercase names are things that only exist at runtime
(define-extended-language Dada dada
  (Program (program Store Expr))
  (Store (Stack Heap Ref-counts))
  (Stack (stack Stack-value ...))
  (Stack-value (x Value))
  (Heap (heap Heap-value ...))
  (Heap-value (Address Value))
  (Ref-counts (ref-counts Ref-count ...))
  (Ref-count (Identity number))
  (Value Address Data)
  (Data
   (class-instance Identity ty (Field-value ...))
   (struct-instance ty (Field-value ...))
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

(define-metafunction Dada
  the-stack : Store -> (Stack-value ...)
  [(the-stack ((stack Stack-value ...) _ _)) (Stack-value ...)])

(define-metafunction Dada
  the-heap : Store -> (Heap-value ...)
  [(the-heap (_ (heap Heap-value ...) _)) (Heap-value ...)])

(define-metafunction Dada
  the-ref-counts : Store -> (Ref-count ...)
  [(the-ref-counts (_ _ (ref-counts Ref-count ...))) (Ref-count ...)])

(define-metafunction Dada
  load-stack : Store x -> Data
  [(load-stack Store x) ,(cadr (assoc (term x) (term (the-stack Store))))])

(define-metafunction Dada
  load-heap : Store Address -> Data
  [(load-heap Store Address) ,(cadr (assoc (term Address) (term (the-heap Store))))]
  )

(define-metafunction Dada
  load-ref-count : Store Identity -> number
  [(load-ref-count Store Identity) ,(cadr (assoc (term Identity) (term (the-ref-counts Store))))]
  )

(test-equal (term (load-stack ((stack (foo 22)) (heap) (ref-counts)) foo)) 22)
(test-equal (term (load-heap ((stack) (heap (bar 44)) (ref-counts)) bar)) 44)
(test-equal (term (the-ref-counts ((stack) (heap) (ref-counts (baz 66))))) '((baz 66)))
(test-equal (term (load-ref-count ((stack) (heap) (ref-counts (baz 66))) baz)) 66)

;(define-metafunction Dada
;  deref : Store Value -> Data
;  [(Store Data) Data]
;  [(Store Address) (deref Store (load Store Address))])
;
;(define-metafunction Dada
;  read : store place -> Data
;  [(store (x)) 22])

;(define reductions
;  (reduction-relation
;   Dada
;   (c--> (seq Value expr ...)
;         ,(seq expr ...)
;         "set-step")
;   with
;   [(--> (in-hole Program_1 a) (in-hole Program_1 b))
;    (c--> a b)]))

(test-match Dada Store (term ((stack) (heap) (ref-counts))))
(test-match Dada Stack (term (stack)))
(test-match Dada Heap (term (heap)))
(test-match Dada Ref-counts (term (ref-counts)))
(test-match Dada Expr (term 22))
(test-match Dada Expr (term (seq 22 44 66)))
;(traces reductions
;        (term (program (stack) (heap) (ref-counts) (seq 22 44 66))))
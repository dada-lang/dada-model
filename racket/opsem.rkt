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
  (Value (box Address) Data)
  (Data
   (class-instance Identity ty Field-values)
   (struct-instance ty Field-values)
   number)
  (Field-values (Field-value ...))
  (Field-value (f Value))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic memory access metafunctions

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
  load-stack : Store x -> Value
  [(load-stack Store x) ,(cadr (assoc (term x) (term (the-stack Store))))])

(define-metafunction Dada
  load-heap : Store Address -> Value
  [(load-heap Store Address) ,(cadr (assoc (term Address) (term (the-heap Store))))]
  )

(define-metafunction Dada
  load-ref-count : Store Identity -> number
  [(load-ref-count Store Identity) ,(cadr (assoc (term Identity) (term (the-ref-counts Store))))]
  )

(define-metafunction Dada
  load-field : Store Data f -> Value
  [(load-field Store (class-instance _ _ Field-values) f) ,(cadr (assoc (term f) (term Field-values)))]
  [(load-field Store (struct-instance _ Field-values) f) ,(cadr (assoc (term f) (term Field-values)))]
  )

(define-metafunction Dada
  deref : Store Value -> Data
  [(deref Store (box Address)) (deref Store (load-heap Store Address))]
  [(deref Store Data) Data]
  )

(define-metafunction Dada
  read : Store place -> Data
  [(read Store (x f ...)) (read-fields Store (deref Store (load-stack Store x)) (f ...))]
  )

(define-metafunction Dada
  read-fields : Store Data (f ...) -> Data
  [(read-fields Store Data ()) Data]
  [(read-fields Store Data (f_0 f_1 ...)) (read-fields Store (deref Store (load-field Store Data f_0)) (f_1 ...))])

(let [(store
       (term ((stack (x0 22)
                     (x1 (box a0))
                     (x2 (struct-instance some-struct ((f0 22) (f1 (box a0)))))
                     (x3 (box a1)))
              (heap (a0 44)
                    (a1 (struct-instance some-struct ((f0 22) (f1 (box a0)) (f2 (box a1))))))
              (ref-counts (i0 66)))))]
  (test-match Dada ty 'some-struct)
  (test-match Dada Field-values '((f0 22)))
  (test-match Dada Value '(struct-instance some-struct ((f0 22))))
  (test-match Dada Store store)
  (test-equal (term (load-stack ,store x0)) 22)
  (test-equal (term (load-stack ,store x1)) (term (box a0)))
  (test-equal (term (load-heap ,store a0)) 44)
  (test-equal (term (load-ref-count ,store i0)) 66)
  (test-equal (term (deref ,store (load-stack ,store x1))) 44)
  (test-equal (term (read ,store (x0))) 22)
  (test-equal (term (read ,store (x1))) 44)
  (test-equal (term (read ,store (x2 f0))) 22)
  (test-equal (term (read ,store (x2 f1))) 44)
  (test-equal (term (read ,store (x3 f2 f2 f2 f2 f1))) 44)
  )



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
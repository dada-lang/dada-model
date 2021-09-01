#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         "../grammar.rkt"
         "../type-system.rkt"
         "../util.rkt")
(provide (all-defined-out))

;; Convention: uppercase names are things that only exist at runtime
(define-extended-language Dada dada-type-system
  (Store (Stack Heap Ref-table))
  (Stack (stack Stack-values))
  (Stack-values (Stack-value ...))
  (Stack-value (x Value))
  (Heap (heap Heap-values))
  (Heap-values (Heap-value ...))
  (Heap-value (Address Value))
  (Ref-table (ref-table Ref-counts))
  (Ref-counts (Ref-count ...))
  (Ref-count (Address number))
  (Value (Identity box Address) Unboxed-value expired)
  (Unboxed-value Aggregate number)
  (Aggregate (Identity id Field-values))
  (Field-values (Field-value ...))
  (Field-value (f Value))
  (Identity shared (my Address))
  (Address variable-not-otherwise-mentioned)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic memory access metafunctions

(define-metafunction Dada
  the-stack : Store -> Stack-values
  [(the-stack ((stack Stack-values) _ _)) Stack-values])

;; `(with-stack-entry (x Value) Store)` returns a new `Store` with `x` assigned to `Value`.
;;
;; The expectation is that `x` is not already on the stack.
(define-metafunction Dada
  with-stack-entry : Stack-value Store -> Store
  [(with-stack-entry Stack-value_0 ((stack (Stack-value_1 ...)) Heap Ref-table))
   ((stack (Stack-value_0 Stack-value_1 ...)) Heap Ref-table)])

(define-metafunction Dada
  the-heap : Store -> Heap-values
  [(the-heap (_ (heap Heap-values) _)) Heap-values])

(define-metafunction Dada
  the-ref-counts : Store -> Ref-counts
  [(the-ref-counts (_ _ (ref-table Ref-counts))) Ref-counts])

(define-metafunction Dada
  store-with-ref-counts : Store Ref-counts -> Store
  [(store-with-ref-counts (Stack Heap _) Ref-counts)
   (Stack Heap (ref-table Ref-counts))]
  )

(define-metafunction Dada
  load-stack : Store x -> Value
  [(load-stack Store x)
   Value
   (where (_ ... (x Value) _ ...) (the-stack Store))
   ]
  )

;; True if there is no variable named `x`.
(define-metafunction Dada
  fresh-var? : Store x -> boolean
  [(fresh-var? Store x)
   #f
   (where (_ ... (x Value) _ ...) (the-stack Store))]
  [(fresh-var? Store x)
   #t])

(define-metafunction Dada
  load-heap : Store Address -> Value
  [(load-heap Store Address)
   Value
   (where (_ ... (Address Value) _ ...) (the-heap Store))]
  )

(define-metafunction Dada
  load-field : Store Unboxed-value f -> Value
  [(load-field Store (Identity id (_ ... (f Value) _ ...)) f) Value]
  )

(define-metafunction Dada
  deref : Store Value -> Unboxed-value
  [(deref Store (_ box Address)) (deref Store (load-heap Store Address))]
  [(deref Store Unboxed-value) Unboxed-value]
  )

(define-metafunction Dada
  read : Store place -> Value
  [(read Store (x f ...)) (read-fields Store (load-stack Store x) (f ...))]
  )

(define-metafunction Dada
  read-fields : Store Value (f ...) -> Value
  [(read-fields Store Value ()) Value]
  [(read-fields Store Value (f_0 f_1 ...)) (read-fields Store (load-field Store (deref Store Value) f_0) (f_1 ...))])

(module+ test
  (redex-let*
   Dada
   [(Stack (term (stack [(x0 22)
                         (x1 ((my i0) box a0))
                         (x2 ((my i0) some-struct ((f0 22) (f1 ((my i0) box a0)))))
                         (x3 ((my i0) box a1))])))
    (Ref-counts (term [(i0 66)]))
    (Store
     (term (Stack
            (heap [(a0 44)
                   (a1 ((my i0) some-struct ((f0 22) (f1 ((my i0) box a0)) (f2 ((my i0) box a1)))))])
            (ref-table Ref-counts))))]
   (test-equal (term (load-stack Store x0)) 22)
   (test-equal (term (fresh-var? Store x0)) #f)
   (test-equal (term (fresh-var? Store not-a-var)) #t)
   (test-equal (term (load-stack Store x1)) (term ((my i0) box a0)))
   (test-equal (term (load-heap Store a0)) 44)
   (test-equal (term (deref Store (load-stack Store x1))) 44)
   (test-equal (term (read Store (x0))) 22)
   (test-equal (term (read Store (x1))) (term ((my i0) box a0)))
   (test-equal (term (deref Store (read Store (x1)))) 44)
   (test-equal (term (read Store (x2 f0))) 22)
   (test-equal (term (deref Store (read Store (x2 f1)))) 44)
   (test-equal (term (deref Store (read Store (x3 f2 f2 f2 f2 f1)))) 44)
   )
  )
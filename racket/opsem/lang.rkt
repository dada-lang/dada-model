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
;; If `x` is already on the stack, it is overwritten.
(define-metafunction Dada
  with-stack-entry : Stack-value Store -> Store

  [(with-stack-entry (x Value) ((stack (Stack-value_0 ... (x Value_old) Stack-value_1 ...)) Heap Ref-table))
   ((stack (Stack-value_0 ... (x Value) Stack-value_1 ...)) Heap Ref-table)]
  
  [(with-stack-entry Stack-value_0 ((stack (Stack-value_1 ...)) Heap Ref-table))
   ((stack (Stack-value_0 Stack-value_1 ...)) Heap Ref-table)]
  )

(define-metafunction Dada
  the-heap : Store -> Heap-values
  [(the-heap (_ (heap Heap-values) _)) Heap-values])

(define-metafunction Dada
  store-with-heap-entry : Store Heap-value -> Store

  [(store-with-heap-entry (Stack (heap (Heap-value_0 ... (Address Value_old) Heap-value_1 ...)) Ref-table) (Address Value))
   (Stack (heap (Heap-value_0 ... (Address Value) Heap-value_1 ...)) Ref-table)]

  [(store-with-heap-entry (Stack (heap (Heap-value_1 ...)) Ref-table) Heap-value_0)
   (Stack (heap (Heap-value_0 Heap-value_1 ...)) Ref-table)]
  )

(define-metafunction Dada
  the-ref-counts : Store -> Ref-counts
  [(the-ref-counts (_ _ (ref-table Ref-counts))) Ref-counts])

(define-metafunction Dada
  store-with-ref-counts : Store Ref-counts -> Store
  [(store-with-ref-counts (Stack Heap _) Ref-counts)
   (Stack Heap (ref-table Ref-counts))]
  )

;; True if there is no variable named `x`.
(define-metafunction Dada
  fresh-var? : Store x -> boolean
  [(fresh-var? Store x)
   #f
   (where (_ ... (x Value) _ ...) (the-stack Store))]
  [(fresh-var? Store x)
   #t])

(module+ test
  (redex-let*
   Dada
   [(Store
     (term ((stack [(x0 22)])
            (heap [])
            (ref-table []))))]
   (test-equal (term (fresh-var? Store x0)) #f)
   (test-equal (term (fresh-var? Store not-a-var)) #t)
   )
  )
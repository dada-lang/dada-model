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
  (Stack (stack Stack-mappings))
  (Stack-mappings (Stack-mapping ...))
  (Stack-mapping (x Value))
  (Heap (heap Heap-mappings))
  (Heap-mappings (Heap-mapping ...))
  (Heap-mapping (Address Value))
  (Ref-table (ref-table Ref-mappings))
  (Ref-mappings (Ref-mapping ...))
  (Ref-mapping (Address number))
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
  the-stack : Store -> Stack-mappings
  [(the-stack ((stack Stack-mappings) _ _)) Stack-mappings])

;; `(with-stack-entry (x Value) Store)` returns a new `Store` with `x` assigned to `Value`.
;;
;; If `x` is already on the stack, it is overwritten.
(define-metafunction Dada
  with-stack-entry : Stack-mapping Store -> Store

  [(with-stack-entry (x Value) ((stack (Stack-mapping_0 ... (x Value_old) Stack-mapping_1 ...)) Heap Ref-table))
   ((stack (Stack-mapping_0 ... (x Value) Stack-mapping_1 ...)) Heap Ref-table)]
  
  [(with-stack-entry Stack-mapping_0 ((stack (Stack-mapping_1 ...)) Heap Ref-table))
   ((stack (Stack-mapping_0 Stack-mapping_1 ...)) Heap Ref-table)]
  )

(define-metafunction Dada
  the-heap : Store -> Heap-mappings
  [(the-heap (_ (heap Heap-mappings) _)) Heap-mappings])

(define-metafunction Dada
  store-with-heap-entry : Store Heap-mapping -> Store

  [(store-with-heap-entry (Stack (heap (Heap-mapping_0 ... (Address Value_old) Heap-mapping_1 ...)) Ref-table) (Address Value))
   (Stack (heap (Heap-mapping_0 ... (Address Value) Heap-mapping_1 ...)) Ref-table)]

  [(store-with-heap-entry (Stack (heap (Heap-mapping_1 ...)) Ref-table) Heap-mapping_0)
   (Stack (heap (Heap-mapping_0 Heap-mapping_1 ...)) Ref-table)]
  )

(define-metafunction Dada
  the-ref-counts : Store -> Ref-mappings
  [(the-ref-counts (_ _ (ref-table Ref-mappings))) Ref-mappings])

(define-metafunction Dada
  store-with-ref-counts : Store Ref-mappings -> Store
  [(store-with-ref-counts (Stack Heap _) Ref-mappings)
   (Stack Heap (ref-table Ref-mappings))]
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
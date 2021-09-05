#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         "../grammar.rkt"
         "../type-system.rkt"
         "../util.rkt")
(provide (all-defined-out))

;; Convention: uppercase names are things that only exist at runtime
(define-extended-language Dada dada-type-system
  (Store (Stack-mappings Heap-mappings))
  (Stack-mappings (Stack-mapping ...))
  (Stack-mapping (x Value))
  (Heap-mappings (Heap-mapping ...))
  (Heap-mapping (Address Boxed-value))
  (Boxed-value (box Ref-count Unboxed-value))
  (Ref-count number)
  (Value (Ownership box Address) number expired)
  (Ownership my shared)
  (Unboxed-value Aggregate Value)
  (Aggregate (id Field-values))
  (Field-values (Field-value ...))
  (Field-value (f Value))
  (Address variable-not-otherwise-mentioned)

  ; Small step
  (Evaluated-expr Value)
  (Exprs (Evaluated-expr ... Expr expr ...))
  (Expr hole
        (var x = Expr)
        (set place-at-rest = Expr)
        (call m params Exprs)
        (data-instance dt params Exprs)
        (class-instance c params Exprs)
        (share Place-at-rest)
        (lend Place-at-rest)
        (give Place-at-rest)
        (copy Place-at-rest)
        (seq (Expr expr ...))
        (atomic Expr)
        (Expr : ty)
        (assert-ty Place-at-rest : ty)
        )
  (Place-at-rest hole)
  )

(define-term Store_empty ([] []))
(test-match Dada Store (term Store_empty))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic memory access metafunctions

(define-metafunction Dada
  the-stack : Store -> Stack-mappings
  [(the-stack (Stack-mappings _)) Stack-mappings])

;; `(with-stack-entry (x Value) Store)` returns a new `Store` with `x` assigned to `Value`.
;;
;; If `x` is already on the stack, it is overwritten.
(define-metafunction Dada
  store-with-stack-mapping : Store Stack-mapping -> Store

  [(store-with-stack-mapping ((Stack-mapping_0 ... (x _) Stack-mapping_1 ...) Heap-mappings) (x Value))
   ((Stack-mapping_0 ... (x Value) Stack-mapping_1 ...) Heap-mappings)]
  
  [(store-with-stack-mapping ((Stack-mapping_1 ...) Heap-mappings) Stack-mapping_0)
   ((Stack-mapping_0 Stack-mapping_1 ...) Heap-mappings)]
  )

(define-metafunction Dada
  store-with-stack-mappings : Store Stack-mapping ... -> Store

  [(store-with-stack-mappings Store) Store]

  [(store-with-stack-mappings Store Stack-mapping_0 Stack-mapping_1 ...)
   (store-with-stack-mappings (store-with-stack-mapping Store Stack-mapping_0) Stack-mapping_1 ...)]
  )

(define-metafunction Dada
  the-heap : Store -> Heap-mappings
  [(the-heap (_ Heap-mappings)) Heap-mappings])

(define-metafunction Dada
  store-with-heap : Store Heap-mappings -> Store
  [(store-with-heap (Stack-mappings _) Heap-mappings) (Stack-mappings Heap-mappings)])

(define-metafunction Dada
  ;; store-with-heap-entry
  ;;
  ;; Returns a new store that contains Heap-mapping (overwrites any old Heap-mapping
  ;; with the same address).
  store-with-heap-entry : Store Heap-mapping -> Store

  [(store-with-heap-entry (Stack-mappings (Heap-mapping_0 ... (Address _) Heap-mapping_1 ...)) (Address Boxed-value))
   (Stack-mappings (Heap-mapping_0 ... (Address Boxed-value) Heap-mapping_1 ...))]

  [(store-with-heap-entry (Stack-mappings (Heap-mapping_1 ...)) Heap-mapping_0)
   (Stack-mappings (Heap-mapping_0 Heap-mapping_1 ...))]
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
  ;; load-heap
  ;;
  ;; Load the Unboxed-value for the box at a given Address.
  load-heap : Store Address -> Unboxed-value
  [(load-heap Store Address)
   Unboxed-value
   (where (_ ... (Address (box _ Unboxed-value)) _ ...) (the-heap Store))]
  )

(define-metafunction Dada
  ;; load-ref-count
  ;;
  ;; Load the ref-count for the box at a given Address.
  load-ref-count : Store Address -> Ref-count

  [(load-ref-count Store Address)
   Ref-count
   (where (_ ... (Address (box Ref-count _)) _ ...) (the-heap Store))]
  )


(module+ test
  (redex-let*
   Dada
   [(Store
     (term ([(x0 (my box alpha))]
            [(alpha (box 1 20))]
            )))]
   (test-equal (term (fresh-var? Store x0)) #f)
   (test-equal (term (fresh-var? Store not-a-var)) #t)
   )
  )
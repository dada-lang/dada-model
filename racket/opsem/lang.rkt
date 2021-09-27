#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         "../grammar.rkt"
         "../type-system.rkt"
         "../util.rkt")
(provide (all-defined-out))

;; Convention: uppercase names are things that only exist at runtime
(define-extended-language Dada dada-type-system
  (Store (Stack-segments Heap-mappings Lease-mappings))
  (Stack-segments (Stack-segment ...))
  (Stack-segment Stack-mappings)
  (Stack-mappings (Stack-mapping ...))
  (Stack-mapping (x Value))
  (Heap-mappings (Heap-mapping ...))
  (Heap-mapping (Address Boxed-value))
  (Boxed-value (box Ref-count Unboxed-value))
  (Ref-count number)
  (Values (Value ...))
  (Value (Ownership box Address) number expired)
  (Ownership my (leased Lease))
  (Unboxed-value Aggregate Value)
  (Aggregate (Aggregate-id Field-values))
  (Aggregate-id (class c))
  (Field-values (Field-value ...))
  (Field-value (f Value))
  (Address variable-not-otherwise-mentioned)

  (Leases (Lease ...))
  (Lease variable-not-otherwise-mentioned)
  (Lease-data (Lease-kind Leases Address))
  (Lease-kind shared borrowed)
  
  (Lease-mappings (Lease-mapping ...))
  (Lease-mapping (Lease Lease-data))

  (Action (read-address Ownership Address)
          (write-address Ownership Address)
          (drop-lease Lease)
          (drop-address Address)
          noop)
  (Lease-dependency Lease Address)

  ; Small step
  (Evaluated-expr Value)
  (Exprs (Evaluated-expr ... Expr expr ...))
  (Expr hole
        (var x = Expr)
        (set place-at-rest = Expr)
        (call m params Exprs)
        (class-instance c params Exprs)
        (seq-pushed (Expr expr ...))
        (atomic Expr)
        (Expr : ty)
        )
  )

(define-term Store_empty ([[]] [] []))
(test-match Dada Store (term Store_empty))

(define-metafunction Dada
  ownership-leases : Ownership -> (Lease ...)
  
  [(ownership-leases my) ()]
  [(ownership-leases (leased Lease)) (Lease)]
  )
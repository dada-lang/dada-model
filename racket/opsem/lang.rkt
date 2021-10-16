#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         "../grammar.rkt")
(provide (all-defined-out))

;; Convention: uppercase names are things that only exist at runtime
(define-extended-language Dada dada
  (Store (Stack-segments Heap-mappings Lease-mappings))
  (Stack-segments (Stack-segment ...))
  (Stack-segment Stack-mappings)
  (Stack-mappings (Stack-mapping ...))
  (Stack-mapping (x Value))
  (Heap-mappings (Heap-mapping ...))
  (Heap-mapping (Address Heap-value))
  (Heap-value (box Ref-count Unboxed-value))
  (Ref-count number static)
  (Values (Value ...))
  (Value Box-value expired)
  (Box-value (Permission box Address))
  (Permission Owned-kind (Lease-kind Lease))
  (Owned-kind my our)
  (Unboxed-value Aggregate number Value)
  (Aggregate (Aggregate-id Field-values))
  (Aggregate-id (class c))
  (Field-values (Field-value ...))
  (Field-value (f Value))
  (Address variable-not-otherwise-mentioned)

  (Traversal (Traversal-origin = Box-value))
  (Traversal-origin x (Traversal f mutability))
  (; a traversal that potentially reaches an expired value;
   ; note that this can only occur at the outermost level
   Traversal-e (Traversal-origin = Value))

  (Access-permissions (Owned-kind atomic? Leases))

  (Leases (Lease ...))
  (Lease variable-not-otherwise-mentioned)
  (Lease-data (Lease-kind Leases Address))
  (Lease-kind shared lent)

  (Lease-mappings (Lease-mapping ...))
  (Lease-mapping (Lease Lease-data))

  (Actions (Action ...))
  (Action (read-address Permission Address)
          (write-address Permission Address)
          (update-address Address Unboxed-value)
          (update-local x Value)
          (share-lease Lease)
          (copy-address Address)
          noop)
  (Fallible-actions (Fallible-action ...))
  (Fallible-action Action expired)

  ; Small step
  (Evaluated-expr Value)
  (Exprs (Evaluated-expr ... Expr expr ...))
  (Expr hole
        (var x = Expr)
        (set place-at-rest = Expr)
        (share Expr)
        (call m params Exprs)
        (class-instance c params Exprs)
        (seq-pushed (Expr expr ...))
        (atomic Expr)
        (Expr : ty)
        )
  (; the final "any" here should be an Expr, but possibly with values in the hole etc,
   ; and I don't know how to express that!
   Config (program Store any))
  )

(define-term Store_empty ([[]] [(the-Zero (box static 0))] []))
(test-match Dada Store (term Store_empty))

(; some parts of the semantics rely on having access to a value `0`;
 ; therefore we just add one into the store with a static ref count
 ; (so it can just be freely referenced).
 define-term the-Zero-value (our box the-Zero))
(test-match Dada Value (term the-Zero-value))

(define (outer-seq-complete? config)
  ; Predicate that evaluates to #t if this configuration represents *just* a sequence with a final
  ; value. This is often the state where we want to stop and observe the state for
  ; testing purposes: if we take one more step, we will pop the outer seq and free most
  ; of the heap.
  (define-metafunction Dada
    outer-seq-complete-term? : any -> boolean

    [(outer-seq-complete-term? (program Store (seq-pushed (Value)))) #t]
    [(outer-seq-complete-term? any) #f]
    )
  (term (outer-seq-complete-term? ,config)))


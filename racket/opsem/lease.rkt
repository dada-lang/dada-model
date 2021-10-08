#lang racket
(require redex
         "../grammar.rkt"
         "../util.rkt"
         "lang.rkt"
         "clone.rkt"
         "stack.rkt"
         "heap.rkt")

(provide invalidate-leases-in-store
         create-lease-mapping
         store-with-lease-mappings
         kind-of-lease)

(define-metafunction Dada
  ;; store-with-lease-mappings
  store-with-lease-mappings : Store Lease-mappings -> Store
  [(store-with-lease-mappings (Stack-segments Heap-mappings _) Lease-mappings) (Stack-segments Heap-mappings Lease-mappings)])

(define-metafunction Dada
  ;; lease-mappings-in-store
  lease-mappings-in-store : Store -> Lease-mappings
  [(lease-mappings-in-store (_ _ Lease-mappings)) Lease-mappings])

(define-metafunction Dada
  ;; kind-of-lease
  ;;
  ;; Looks up the 'kind' of a lease
  kind-of-lease : Store Lease -> Lease-kind
  [(kind-of-lease Store Lease)
   Lease-kind
   (where/error (Lease-kind _ _) (lease-data-in-Store Store Lease))])

(define-metafunction Dada
  ;; lease-data-in-Store
  lease-data-in-Store : Store Lease -> Lease-data
  [(lease-data-in-Store Store Lease)
   (lease-data-in-mappings (lease-mappings-in-store Store) Lease)])

(define-metafunction Dada
  ;; lease-data-in-mappings
  lease-data-in-mappings : Lease-mappings Lease -> Lease-data
  [(lease-data-in-mappings Lease-mappings Lease)
   Lease-data
   (where (_ ... (Lease Lease-data) _ ...) Lease-mappings)])

(define-metafunction Dada
  ;; create-lease-mapping
  create-lease-mapping : Store Lease-kind Leases Address -> (Lease Store)
  [(create-lease-mapping Store Lease-kind Leases Address)
   (Lease (store-with-lease-mappings Store (Lease-mapping ... (Lease (Lease-kind Leases Address)))))
   (where/error (Lease-mapping ...) (lease-mappings-in-store Store))
   (where/error Lease ,(variable-not-in (term Store) 'Lease-id))])

(define-metafunction Dada
  ;; invalidate-leases-in-store
  ;;
  ;; Modifies the Store to exclude all leases directly
  ;; or indirectly invalidated by the given action.
  invalidate-leases-in-store : Store Action -> Store

  [(invalidate-leases-in-store Store Action)
   (Stack-segments_out Heap-mappings_out Lease-mappings_out)
   (where/error Lease-mappings_in (lease-mappings-in-store Store))
   (where/error Lease-mappings_out (invalidate-lease-mappings-fix Lease-mappings_in Action))
   (where/error Stack-segments_out (expire-leased-references-in-stack Lease-mappings_out (stack-segments-in-store Store)))
   (where/error Heap-mappings_out (expire-leased-references-in-heap Lease-mappings_out (the-heap Store)))
   ]

  )

(define-metafunction Dada
  ;; invalidate-lease-mappings-fix
  ;;
  ;; Extends invalidate-lease-mappings to include indirect effects.
  invalidate-lease-mappings-fix : Lease-mappings Action -> Lease-mappings

  [; Fixed point reached.
   (invalidate-lease-mappings-fix Lease-mappings_in Action)
   Lease-mappings_in
   (where Lease-mappings_in (invalidate-lease-mappings Lease-mappings_in Action))
   ]

  [; Remove anything due to Action and then recurse till fixed point is reached
   (invalidate-lease-mappings-fix Lease-mappings_in Action)
   (invalidate-lease-mappings-fix Lease-mappings_out noop)
   (where/error Lease-mappings_out (invalidate-lease-mappings Lease-mappings_in Action))
   ]
  )

(define-metafunction Dada
  ;; invalidate-lease-mappings
  ;;
  ;; Given a list of lease-mappings and an action, returns a new list
  ;; that excludes those lease-mappings which are directly invalidated
  ;; by action.
  invalidate-lease-mappings : Lease-mappings Action -> Lease-mappings

  [(invalidate-lease-mappings Lease-mappings_in Action)
   (Lease-mapping_out ... ...)
   (where/error (Lease-mapping_in ...) Lease-mappings_in)
   (where/error ((Lease-mapping_out ...) ...) ((invalidate-lease-mapping Lease-mappings_in Action Lease-mapping_in) ...))
   ]

  )

(define-metafunction Dada
  ;; invalidate-lease-mapping
  ;;
  ;; Given
  ;;
  ;; * a list of the currently valid lease-mappings
  ;; * an action that took place
  ;; * Lease-mapping, one of those currently valid lease-mappings in the list
  ;;
  ;; returns either `()` (if the lease is invalidated) or `(Lease-mapping)` otherwise.
  invalidate-lease-mapping : Lease-mappings Action Lease-mapping -> Lease-mappings

  [; Writes invalidate both shared/lent (unless they take place through the lease itself)
   (invalidate-lease-mapping Lease-mappings (write-address Ownership Address) (Lease (Lease-kind _ Address)))
   ()
   (where #f (via-lease Lease-mappings Ownership Lease))]

  [; Reads invalidate lent (unless they take place through the lease itself)
   (invalidate-lease-mapping Lease-mappings (read-address Ownership Address) (Lease (lent _ Address)))
   ()
   (where #f (via-lease Lease-mappings Ownership Lease))]

  [; Dropping a lent lease invalidates it.
   (invalidate-lease-mapping Lease-mappings (drop-lease Lease) (Lease (lent _ _)))
   ()]

  [; Dropping an address invalidates any leases of it.
   (invalidate-lease-mapping Lease-mappings (drop-address Address) (Lease (_ _ Address)))
   ()]

  [; Noop invalidates any sublease of a "no-longer-valid" lease
   (invalidate-lease-mapping Lease-mappings noop (_ (Lease-kind (_ ... Lease_parent _ ...) Address)))
   ()
   (where #f (lease-valid Lease-mappings Lease_parent))
   ]

  [; Otherwise the lease remains valid
   (invalidate-lease-mapping Lease-mappings Action Lease-mapping)
   (Lease-mapping)]
  )

(define-metafunction Dada
  ;; lease-valid
  ;;
  ;; True if a lease with the given dependencies is dependent on the given dependency.
  lease-valid : Lease-mappings Lease -> boolean

  [(lease-valid (_ ... (Lease _) _ ...) Lease) #t]
  [(lease-valid Lease-mappings Lease) #f]
  )

(define-metafunction Dada
  ;; leases-include
  ;;
  ;; True if a lease with the given dependencies is dependent on the given dependency.
  leases-include : Leases Lease -> boolean

  [(leases-include (_ ... Lease _ ...) Lease) #t]
  [(leases-include _ Lease) #f]
  )

(define-metafunction Dada
  ;; via-lease
  ;;
  ;; True if a write through a box with the given Ownership
  ;; was a write through this lease.
  via-lease : Lease-mappings Ownership Lease -> boolean

  [(via-lease Lease-mappings Ownership Lease)
   (leases-include Leases_parents Lease)
   (where/error Leases_parents (ownership-transitive-leases Lease-mappings Ownership))]
  )

(define-metafunction Dada
  ;; ownership-transitive-leases
  ownership-transitive-leases : Lease-mappings Ownership -> (Lease ...)
  [(ownership-transitive-leases Lease-mappings my) ()]
  [(ownership-transitive-leases Lease-mappings (Lease-kind Lease)) (parent-leases Lease-mappings Lease)])

(define-metafunction Dada
  ;; parent-leases
  ;;
  ;; Looks up the 'kind' of a lease
  parent-leases : Lease-mappings Lease -> (Lease ...)
  [(parent-leases Lease-mappings Lease)
   (Lease Lease_parent1 ... ...)
   (where/error (_ (Lease_parent0 ...) _) (lease-data-in-mappings Lease-mappings Lease))
   (where/error ((Lease_parent1 ...) ...) ((parent-leases Lease-mappings Lease_parent0) ...))])

(define-metafunction Dada
  ;; expire-leased-references-in-value
  ;;
  ;; Looks up the 'kind' of a lease
  expire-leased-references-in-value : Lease-mappings Unboxed-value -> Unboxed-value

  [(expire-leased-references-in-value Lease-mappings (Owned-kind box Address)) (Owned-kind box Address)]

  [(expire-leased-references-in-value Lease-mappings ((Lease-kind Lease) box Address))
   ((Lease-kind Lease) box Address)
   (where #t (lease-valid Lease-mappings Lease))]

  [(expire-leased-references-in-value Lease-mappings ((Lease-kind Lease) box Address))
   expired
   (where/error #f (lease-valid Lease-mappings Lease))]

  [(expire-leased-references-in-value Lease-mappings number)
   number]

  [(expire-leased-references-in-value Lease-mappings expired)
   expired]

  [(expire-leased-references-in-value Lease-mappings (Aggregate-id ((f Value) ...)))
   (Aggregate-id ((f Value_expired) ...))
   (where/error (Value_expired ...) ((expire-leased-references-in-value Lease-mappings Value) ...))]
  )

(define-metafunction Dada
  ;; expire-leased-references-in-stack
  ;;
  ;; Looks up the 'kind' of a lease
  expire-leased-references-in-stack : Lease-mappings Stack-segments -> Stack-segments

  [(expire-leased-references-in-stack Lease-mappings [[(x Value) ...] ...])
   [[(x Value_expired) ...] ...]
   (where/error ((Value_expired ...) ...) (((expire-leased-references-in-value Lease-mappings Value) ...) ...))
   ]
  )

(define-metafunction Dada
  ;; expire-leased-references-in-heap
  ;;
  ;; Looks up the 'kind' of a lease
  expire-leased-references-in-heap : Lease-mappings Heap-mappings -> Heap-mappings

  [(expire-leased-references-in-heap Lease-mappings [(Address (box Ref-count Unboxed-value)) ...])
   ((Address (box Ref-count Unboxed-value_expired)) ...)
   (where/error (Unboxed-value_expired ...) ((expire-leased-references-in-value Lease-mappings Unboxed-value) ...))
   ]
  )

(module+ test
  (redex-let*
   Dada
   [(Lease-mappings (term [(Lease-0 (shared () Address-0))
                           (Lease-1 (lent () Address-1))
                           (Lease-1-0 (lent (Lease-1) Address-2))]))]

   (test-equal-terms (invalidate-lease-mappings-fix Lease-mappings (write-address my Address-0))
                     [(Lease-1 (lent () Address-1))
                      (Lease-1-0 (lent (Lease-1) Address-2))]
                     )

   (test-equal-terms (invalidate-lease-mappings-fix Lease-mappings (write-address (shared Lease-0) Address-0))
                     [(Lease-0 (shared () Address-0))
                      (Lease-1 (lent () Address-1))
                      (Lease-1-0 (lent (Lease-1) Address-2))]
                     )

   (test-equal-terms (invalidate-lease-mappings-fix Lease-mappings (write-address my Address-1))
                     [(Lease-0 (shared () Address-0))]
                     )

   (test-equal-terms (invalidate-lease-mappings-fix Lease-mappings (read-address my Address-1))
                     [(Lease-0 (shared () Address-0))]
                     )
   )

  (redex-let*
   Dada
   [(Store_stack (term (store-with-vars Store_empty
                                        (x ((lent Lease-id) box deadbeef))
                                        (y (my box deadbeef)))))
    (Store_leases (term (store-with-lease-mappings Store_stack
                                                   [(Lease-id (lent () deadbeef))])))]
   (test-equal-terms (invalidate-leases-in-store
                      Store_leases
                      (write-address my deadbeef))
                     (store-with-vars Store_empty (x expired) (y (my box deadbeef))))
   )
  )
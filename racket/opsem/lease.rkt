#lang racket
(require redex
         "../grammar.rkt"
         "../type-system.rkt"
         "../util.rkt"
         "lang.rkt"
         "clone.rkt"
         "stack.rkt"
         "heap.rkt")

(provide invalidate-lease-mappings)

(define-metafunction Dada
  ;; store-with-lease-mappings
  store-with-lease-mappings : Store Lease-mappings -> Store
  [(store-with-lease-mappings (Stack-segments Heap-mappings _) Lease-mappings) (Stack-segments Heap-mappings Lease-mappings)])

(define-metafunction Dada
  ;; store-with-lease-mappings
  lease-mappings-in-store : Store -> Lease-mappings
  [(lease-mappings-in-store (_ _ Lease-mappings)) Lease-mappings])

(define-metafunction Dada
  ;; invalidate-lease-mappings
  ;;
  ;; Modifies the Store to exclude all leases directly
  ;; or indirectly invalidated by the given action.
  invalidate-leases-in-store : Store Action -> Store

  [(invalidate-leases-in-store Store Action)
   (store-with-lease-mappings Store Lease-mappings_out)
   (where/error Lease-mappings_in (lease-mappings-in-store Store))
   (where/error Lease-mappings_out (invalidate-lease-mappings-fix Lease-mappings_in Action))
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

  [; Writes invalidate both shared/borrowed
   (invalidate-lease-mapping Lease-mappings (write-address Address) (_ (Lease-kind _ Address)))
   ()]

  [; Writes invalidate both shared/borrowed
   (invalidate-lease-mapping Lease-mappings (write-lease Lease_written) (_ (Lease-kind Leases_parents _)))
   ()
   (where #t (leases-include Leases_parents Lease_written))
   ]

  [; Reads invalidate both borrowed
   (invalidate-lease-mapping Lease-mappings (read-address Address) (_ (borrowed _ Address)))
   ()]

  [; Writes invalidate both shared/borrowed
   (invalidate-lease-mapping Lease-mappings (read-lease Lease_read) (_ (borrowed Leases_parents _)))
   ()
   (where #t (leases-include Leases_parents Lease_read))
   ]  

  [; Noop invalidates any sublease of a "no-longer-valid" lease
   (invalidate-lease-mapping ((Lease_valid _) ...) noop (_ (Lease-kind (_ ... Lease_parent _ ...) Address)))
   ()
   (where #f (leases-include (Lease_valid ...) Lease_parent))
   ]

  [; Otherwise the lease remains valid
   (invalidate-lease-mapping Lease-mappings Action Lease-mapping)
   (Lease-mapping)]
  )

(define-metafunction Dada
  ;; leases-include
  ;;
  ;; True if a lease with the given dependencies is dependent on the given dependency.
  leases-include : Leases Lease -> boolean

  [(leases-include (_ ... Lease _ ...) Lease) #t]
  [(leases-include _ Lease) #f]
  )

(module+ test
  (redex-let*
   Dada
   [(Lease-mappings (term [(Lease-0 (shared () Address-0))
                           (Lease-1 (borrowed () Address-1))
                           (Lease-1-0 (borrowed (Lease-1) Address-2))]))]
    
   (test-equal-terms (invalidate-lease-mappings-fix Lease-mappings (write-address Address-0))
                     [(Lease-1 (borrowed () Address-1))
                      (Lease-1-0 (borrowed (Lease-1) Address-2))]
                     )

   (test-equal-terms (invalidate-lease-mappings-fix Lease-mappings (write-address Address-1))
                     [(Lease-0 (shared () Address-0))]
                     )

   (test-equal-terms (invalidate-lease-mappings-fix Lease-mappings (read-address Address-1))
                     [(Lease-0 (shared () Address-0))]
                     )
   )
  )

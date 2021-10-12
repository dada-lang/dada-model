#lang racket
(require redex
         "lang.rkt"
         "stack.rkt"
         "lease.rkt")
(provide apply-actions-to-store)

(define-metafunction Dada
  apply-actions-to-store : Store Actions -> Store

  [; first, apply each action in turn to Store
   (apply-actions-to-store Store (Action_0 Action_1 ...))
   (apply-actions-to-store Store_0 (Action_1 ...))
   (where/error Store_0 (apply-action-to-store Store Action_0))]

  [; next, apply noop actions...
   (apply-actions-to-store Store ())
   Store
   (where Store (apply-action-to-store Store noop))]

  [; ... until fixed point is reached
   (apply-actions-to-store Store ())
   (apply-actions-to-store Store_0 ())
   (where Store_0 (apply-action-to-store Store noop))]

  )

(define-metafunction Dada
  apply-action-to-store : Store Action -> Store

  [; update-local: modifies the value of a local variable
   (apply-action-to-store Store (update-local x Box-value))
   (store-with-updated-var Store x Box-value)
   ]

  [; otherwise: apply the action recursively to all parts of the store
   (apply-action-to-store Store Action)
   (((Stack-mapping_out ... ...) ...) (Heap-mapping_out ... ...) (Lease-mapping_out ... ...))
   (where/error (((Stack-mapping ...) ...) (Heap-mapping ...) (Lease-mapping ...)) Store)
   (where/error (((Stack-mapping_out ...) ...) ...) (((apply-action-to-stack-mapping Store Action Stack-mapping) ...) ...))
   (where/error ((Heap-mapping_out ...) ...) ((apply-action-to-heap-mapping Store Action Heap-mapping) ...))
   (where/error ((Lease-mapping_out ...) ...) ((apply-action-to-lease-mapping Store Action Lease-mapping) ...))
   ]
  )

(define-metafunction Dada
  ;; apply-action-to-lease-mapping
  ;;
  ;; Given some Action and a Lease-mapping, returns () if the Lease-mapping
  ;; is invalidated by the Action, and (Lease-mapping) otherwise.
  apply-action-to-lease-mapping : Store Action Lease-mapping -> Lease-mappings

  [; Writes invalidate both shared/lent (unless they take place through the lease itself)
   (apply-action-to-lease-mapping Store (write-address Permission Address) (Lease (Lease-kind _ Address)))
   ()
   (where #f (via-lease Store Permission Lease))]

  [; Reads invalidate lent (unless they take place through the lease itself)
   (apply-action-to-lease-mapping Store (read-address Permission Address) (Lease (lent _ Address)))
   ()
   (where #f (via-lease Store Permission Lease))]

  [; Noop invalidates any sublease of a "no-longer-valid" lease
   (apply-action-to-lease-mapping Store noop (_ (Lease-kind (_ ... Lease_parent _ ...) Address)))
   ()
   (where #f (lease-valid Store Lease_parent))
   ]

  [; Otherwise the lease remains valid
   (apply-action-to-lease-mapping Store Action Lease-mapping)
   (Lease-mapping)]
  )

(define-metafunction Dada
  apply-action-to-heap-mapping : Store Action Heap-mapping -> Heap-mappings

  [; update-address: replace value at Address
   (apply-action-to-heap-mapping Store (update-address Address Unboxed-value) (Address (box Ref-count _)))
   ((Address (box Ref-count Unboxed-value)))
   ]

  [; otherwise: apply the action to the value
   (apply-action-to-heap-mapping Store Action (Address (box Ref-count Unboxed-value)))
   ((Address (box Ref-count (apply-action-to-value Store Action Unboxed-value))))
   ]
  )

(define-metafunction Dada
  apply-action-to-stack-mapping : Store Action Stack-mapping -> Stack-mappings

  [(apply-action-to-stack-mapping Store Action (x Value))
   ((x (apply-action-to-value Store Action Value)))
   ]
  )

(define-metafunction Dada
  apply-action-to-value : Store Action Unboxed-value -> Unboxed-value

  [(apply-action-to-value Store Action (Owned-kind box Address)) (Owned-kind box Address)]

  [(apply-action-to-value Store noop ((Lease-kind Lease) box Address))
   ((Lease-kind Lease) box Address)
   (where #t (lease-valid Store Lease))]

  [(apply-action-to-value Store noop ((Lease-kind Lease) box Address))
   expired
   (where/error #f (lease-valid Store Lease))]

  [(apply-action-to-value Store Action (Aggregate-id ((f Value) ...)))
   (Aggregate-id ((f Value_0) ...))
   (where/error (Value_0 ...) ((apply-action-to-value Store Action Value) ...))]

  [(apply-action-to-value Store Action Unboxed-value)
   Unboxed-value]
  )

(define-metafunction Dada
  ;; lease-valid
  ;;
  ;; True if the lease is defined in the Store.
  lease-valid : Store Lease -> boolean

  [(lease-valid Store Lease)
   #t
   (where (_ ... (Lease _) _ ...) (lease-mappings-in-store Store))
   ]

  [(lease-valid Store Lease)
   #f
   ]

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
  ;; True if a write through a box with the given Permission
  ;; was a write through this lease.
  via-lease : Store Permission Lease -> boolean

  [(via-lease Store Permission Lease)
   (leases-include Leases_parents Lease)
   (where/error Leases_parents (permission-transitive-leases Store Permission))]
  )

(define-metafunction Dada
  ;; permission-transitive-leases
  ;;
  ;; Returns the set of leases that "authorize" accesses through this permission:
  ;; * Given an owned Permission, returns ().
  ;; * Given a leased Permission with lease L, returns the transitive parents of L.
  permission-transitive-leases : Store Permission -> (Lease ...)
  [(permission-transitive-leases Store my) ()]
  [(permission-transitive-leases Store (Lease-kind Lease)) (parent-leases Store Lease)])

(define-metafunction Dada
  ;; parent-leases
  ;;
  ;; Transitive parents of a lease.
  parent-leases : Store Lease -> (Lease ...)
  [(parent-leases Store Lease)
   (Lease Lease_parent1 ... ...)
   (where/error (_ (Lease_parent0 ...) _) (lease-data-in-store Store Lease))
   (where/error ((Lease_parent1 ...) ...) ((parent-leases Lease-mappings Lease_parent0) ...))])


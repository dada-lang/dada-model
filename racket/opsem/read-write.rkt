#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         data/order
         "../util.rkt"
         "lang.rkt"
         "stack.rkt"
         "heap.rkt"
         "lease.rkt"
         "clone.rkt"
         "traverse.rkt"
         "action.rkt")

(provide give-place
         swap-place
         share-place
         lend-place
         move-place
         freeze-value)

(define-metafunction Dada
  load-field : Store Unboxed-value f -> Value
  [(load-field Store (_ (_ ... (f Value) _ ...)) f) Value]
  )

(define-metafunction Dada
  ;; deref
  ;;
  ;; Derefs through any boxes
  deref : Store Unboxed-value -> Unboxed-value
  [(deref Store (_ box Address)) (deref Store (load-heap Store Address))]
  [(deref Store Unboxed-value) Unboxed-value]
  )

(define-metafunction Dada
  ;; move-place
  ;;
  ;; Reads the value stored at the given place.
  ;;
  ;; Returns the value along with the set of leases that were traversed to reach it.
  move-place : program Store place -> (Store Value) or expired

  [(move-place program Store place)
   (share-place program Store place)
   (where Traversal (traversal program Store place))
   (where (our _ _) (access-permissions Traversal))
   ]

  [(move-place program Store place)
   (give-place program Store place)
   (where Traversal (traversal program Store place))
   (where (my _ ()) (access-permissions Traversal))
   ]

  [(move-place program Store place)
   (lend-place program Store place)
   (where Traversal (traversal program Store place))
   (where (my _ (Lease_0 Lease_1 ...)) (access-permissions Traversal))
   ]

  [(move-place program Store place)
   expired
   (where expired (traversal program Store place))]

  )

(define-metafunction Dada
  unique-traversal? : Traversal -> boolean

  [(unique-traversal? (_ = (Permission box _)))
   #f
   (where #f (unique-permission? Permission))]

  [(unique-traversal? ((_ f shared) = _))
   #f]

  [(unique-traversal? ((Traversal f _) = _))
   (unique-traversal? Traversal)]

  [(unique-traversal? (x = _))
   #t]

  )

(define-metafunction Dada
  owned-traversal? : Traversal -> boolean

  [(owned-traversal? (_ = (Permission box _)))
   #f
   (where #f (owned-permission? Permission))]

  [(owned-traversal? ((Traversal f _) = _))
   (owned-traversal? Traversal)]

  [(owned-traversal? (x = _))
   #t]

  )

(define-metafunction Dada
  give-place : program Store place -> (Store Value_old) or expired

  [(give-place program Store place)
   (swap-place program Store place expired)]
  )

(define-metafunction Dada
  swap-place : program Store place Value_new -> (Store Value_old) or expired

  [(swap-place program Store place Value_new)
   (Store_out Value_old)
   (where Traversal-e (traversal-e program Store place))
   (where (Actions Value_old) (swap-traversal Store Traversal-e Value_new))
   (where/error Store_out (apply-actions-to-store Store Actions))]

  [(swap-place program Store place Value_new)
   expired]

  )

(define-metafunction Dada
  share-place : program Store place -> (Store Value_old) or expired

  [; copying something owned, shared
   ;
   ; Subtle: note that no atomic access perms are accepted here.
   ; This does not mean you cannot copy things in atomic fields;
   ; but it does mean you can't copy a `my` thing in an atomic field.
   (share-place program Store place)
   (Store_out (our box Address))
   (where Traversal (traversal program Store place))
   (where (our () ()) (access-permissions Traversal))
   (where ((Action ...) (_ box Address)) (read-traversal Store Traversal))
   (where/error Store_out (apply-actions-to-store Store (Action ... (copy-address Address))))
   ]

  [; copying something from a single shared lease-- repeat same lease
   ;
   ; Subtle: note that no atomic access perms are accepted here.
   ; This does not mean you cannot copy things in atomic fields;
   ; but it does mean you can't copy a `my` thing in an atomic field.
   (share-place program Store place)
   (Store ((shared Lease) box Address))
   (where Traversal (traversal program Store place))
   (where (our () (Lease)) (access-permissions Traversal))
   (where shared (kind-of-lease Store Lease))
   (where/error Address (traversal-address Traversal))
   ]

  [; copying something shared but from at least one lent lease;
   ; this creates a new share
   (share-place program Store place)
   (Store_out ((shared Lease_shared) box Address))
   (where Traversal (traversal program Store place))
   (where/error (_ _ Leases) (access-permissions Traversal))
   (where/error Address (traversal-address Traversal))
   (where/error (Lease_shared Store_out) (create-lease-mapping Store shared Leases Address))
   ]

  [(share-place program Store place)
   expired]

  )

(define-metafunction Dada
  freeze-value : program Store Value -> (Store Value_old)

  [(freeze-value program Store (my box Address))
   (Store (our box Address))
   ]

  [(freeze-value program Store ((lent Lease) box Address))
   (Store_out ((shared Lease) box Address))
   (where/error Store_out (apply-actions-to-store Store ((share-lease Lease))))
   ]

  [(freeze-value program Store (our box Address))
   (our box Address)]

  [(freeze-value program Store ((shared Lease) box Address))
   ((shared Lease) box Address)]

  )

(define-metafunction Dada
  lend-place : program Store place -> (Store Value_old) or expired

  [(lend-place program Store place)
   (Store_out ((lent Lease_shared) box Address))
   (where Traversal (traversal program Store place))
   (; can only lend things that are uniquely accessible
    where #t (unique-traversal? Traversal))
   (where (Actions (_ box Address)) (logical-write-traversal Store Traversal))
   (where/error Store_write (apply-actions-to-store Store Actions))
   (where/error Leases_traversal (leases-from-traversal Traversal))
   (where/error (Lease_shared Store_out) (create-lease-mapping Store_write lent Leases_traversal Address))
   ]

  [(lend-place program Store place)
   expired]

  )

(define-metafunction Dada
  leases-from-traversal : Traversal -> (Lease ...)

  [(leases-from-traversal (Traversal-origin = (Permission box _)))
   (deduplicate-leases (Lease_origin ... Lease_perm ...))
   (where/error (Lease_origin ...) (leases-from-traversal-origin Traversal-origin))
   (where/error (Lease_perm ...) (leases-from-permission Permission))
   ]

  )

(define-metafunction Dada
  leases-from-traversal-origin : Traversal-origin -> (Lease ...)

  [(leases-from-traversal-origin x) ()]
  [(leases-from-traversal-origin (Traversal f _)) (leases-from-traversal Traversal)]
  )

(define-metafunction Dada
  leases-from-permission : Permission -> (Lease ...)

  [(leases-from-permission Owned-kind) ()]
  [(leases-from-permission (Lease-kind Lease)) (Lease)]
  )

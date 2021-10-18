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
         share-value
         lend-place
         )

(define-metafunction Dada
  ;; give-place
  ;;
  ;; Reads the value stored at the given place.
  ;;
  ;; Returns the value along with the set of leases that were traversed to reach it.
  give-place : program Store place -> (Store Value) or expired

  [(give-place program Store place)
   (share-place program Store place)
   (where Traversal (traversal program Store place))
   (where (our () _) (access-permissions Traversal))
   ]

  [(give-place program Store place)
   (swap-place program Store place expired)
   (where Traversal (traversal program Store place))
   (where (my _ ()) (access-permissions Traversal))
   ]

  [(give-place program Store place)
   (lend-place program Store place)
   (where Traversal (traversal program Store place))
   (where (my _ (Lease_0 Lease_1 ...)) (access-permissions Traversal))
   ]

  [(give-place program Store place)
   (lend-place program Store place)
   (where Traversal (traversal program Store place))
   (where (our (atomic) _) (access-permissions Traversal))
   ]

  [(give-place program Store place)
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
  share-value : program Store Value -> (Store Value_old)

  [(share-value program Store (my box Address))
   (Store (our box Address))
   ]

  [(share-value program Store ((lent Lease) box Address))
   (Store_out ((shared Lease) box Address))
   (where/error Store_out (apply-actions-to-store Store ((share-lease Lease))))
   ]

  [(share-value program Store (our box Address))
   (our box Address)]

  [(share-value program Store ((shared Lease) box Address))
   ((shared Lease) box Address)]

  )

(define-metafunction Dada
  lend-place : program Store place -> (Store Value_old) or expired

  [(lend-place program Store place)
   (Store_out ((lent Lease_shared) box Address))
   (where Traversal (traversal program Store place))
   (where Access-permissions (access-permissions Traversal))
   (where #t (mutable-access-permissions? Access-permissions))
   (where (Actions (_ box Address)) (logical-write-traversal Store Traversal))
   (where/error (_ _ Leases_traversal) Access-permissions)
   (where/error Store_write (apply-actions-to-store Store Actions))
   (where/error (Lease_shared Store_out) (create-lease-mapping Store_write lent Leases_traversal Address))
   ]

  [(lend-place program Store place)
   expired]

  )

(define-metafunction Dada
  mutable-access-permissions? : Access-permissions -> boolean

  [(mutable-access-permissions? (my _ _)) #t]
  [(mutable-access-permissions? (our (atomic) _)) #t]
  [(mutable-access-permissions? (our () _)) #f]
  )

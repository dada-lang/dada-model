#lang racket

(require redex
         "../grammar.rkt"
         "../util.rkt"
         "lang.rkt"
         "stack.rkt"
         "heap.rkt"
         "lease.rkt"
         "test-store.rkt")

(provide traversal
         traversal-e
         swap-traversal
         logical-write-traversal
         read-traversal
         owned-permission?
         unique-permission?
         traversal-address
         access-permissions)

;; A **traversal** encodes the path that we walked when evaluating a place.
;;
;; Creating a traversal is a side-effect free operation. It is used to derive
;; the actions that result from reading/writing a place.
;;
;; Example (assume all edges are `my` for simplicity):
;;
;;           ┌──────┐
;;  pair─────┤[Pair]│   ┌───────┐
;;           │ a ───┼──►│[Point]│
;;           │      │   │ x ────┼─► a4 = 22
;;           │ b ───┼─┐ │       │
;;           │      │ │ │ y ────┼─► a5 = 44
;;           └──────┘ │ └───────┘
;;           a1       │ a2
;;                    │
;;                    │
;;                    │ ┌───────┐
;;                    └►│[Point]│
;;                      │ x ────┼─► a6 = 66
;;                      │       │
;;                      │ y ────┼─► a7 = 88
;;                      └───────┘
;;                      a3
;;
;; Source: https://is.gd/c7o2zB
;;
;; The place `pair a x` corresponds to a traversal:
;;
;; ( ( . x shared ) = (my box a4) )
;;     │
;;     ▼
;; ( ( . a var ) = (my box a2) )
;;     │
;;     ▼
;; ( x = (my box a1) )

(define-metafunction Dada
  traversal : program Store place-at-rest -> Traversal-e or expired

  [(traversal program Store place-at-rest)
   Traversal
   (where Traversal (traversal-e program Store place-at-rest))
   ]

  [(traversal program Store place-at-rest)
   expired
   ]

  )

(define-metafunction Dada
  traversal-e : program Store place-at-rest -> Traversal-e or expired

  [(traversal-e program Store (x f ...))
   (traverse-fields program Store (x = Value) (f ...))
   (where Value (var-in-store Store x))
   ]

  )

(define-metafunction Dada
  traverse-fields : program Store Traversal-e (f ...) -> Traversal-e or expired

  [(traverse-fields program Store Traversal-e ())
   Traversal-e
   ]

  [(traverse-fields program Store (_ = expired) (f_0 f_1 ...))
   expired
   ]

  [(traverse-fields program Store Traversal (f_0 f_1 ...))
   (traverse-fields program Store ((Traversal f_0 mutability) = Box-value) (f_1 ...))
   (where (Box-value mutability) (field-from-traversal program Store Traversal f_0))
   ]

  )

(define-metafunction Dada
  field-from-traversal : program Store Traversal f -> (Value mutability)
  [(field-from-traversal program Store Traversal f_0)
   (select-field program Unboxed-value f_0)
   (where/error Address (traversal-address Traversal))
   (where/error Unboxed-value (load-heap Store Address))
   ]
  )

(define-metafunction Dada
  select-field : program Unboxed-value f -> (Value mutability)
  [(select-field program ((class c) (_ ... (f Value) _ ...)) f)
   (Value (class-field-mutability program c f))
   ]
  )

(define-metafunction Dada
  access-permissions : Traversal-e -> Access-permissions

  [(access-permissions Traversal-e)
   (access-permissions-for-traversal Traversal-e (my () ()))
   ]

  )

(define-metafunction Dada
  access-permissions-for-traversal : Traversal-e Access-permissions -> Access-permissions

  [(access-permissions-for-traversal (Traversal-origin = expired) Access-permissions)
   (access-permissions-for-traversal-origin Traversal-origin Access-permissions)
   ]

  [(access-permissions-for-traversal (Traversal-origin = (my box _)) Access-permissions)
   (access-permissions-for-traversal-origin Traversal-origin Access-permissions)
   ]

  [(access-permissions-for-traversal (Traversal-origin = ((lent Lease) box _)) (Owned-kind atomic? Leases))
   (access-permissions-for-traversal-origin Traversal-origin (Owned-kind atomic? (add-lease-to-leases Lease Leases)))
   ]

  [(access-permissions-for-traversal (Traversal-origin = (our box _)) (_ atomic? Leases))
   (our atomic? Leases)
   ]

  [(access-permissions-for-traversal (Traversal-origin = ((shared Lease) box _)) (_ atomic? Leases))
   (our atomic? (add-lease-to-leases Lease Leases))
   ]
  )

(define-metafunction Dada
  access-permissions-for-traversal-origin : Traversal-origin Access-permissions -> Access-permissions

  [(access-permissions-for-traversal-origin x Access-permissions)
   Access-permissions
   ]

  [(access-permissions-for-traversal-origin (Traversal _ var) Access-permissions)
   (access-permissions-for-traversal Traversal Access-permissions)
   ]

  [(access-permissions-for-traversal-origin (Traversal _ shared) (_ atomic? Leases))
   (access-permissions-for-traversal Traversal (our atomic? Leases))
   ]

  [(access-permissions-for-traversal-origin (Traversal _ atomic) (Owned-kind _ Leases))
   (access-permissions-for-traversal Traversal (Owned-kind (atomic) Leases))
   ]
  )

(define-metafunction Dada
  swap-traversal : Store Traversal-e Value -> (Fallible-actions Value_old)

  [; modify local variable: easy
   (swap-traversal Store (x = Value_old) Value_new)
   (((update-local x Value_new)) Value_old)
   ]

  [; modify field: requires field be writable
   (swap-traversal Store (Traversal-origin = Value_old) Value_new)
   ((Fallible-action ... (update-address Address Unboxed-value_new)) Value_old)
   (where/error ((_ = (_ box Address)) f _) Traversal-origin)
   (where/error (Fallible-action ...) (write-traversal-origin Store Traversal-origin))
   (where/error Unboxed-value_old (load-heap Store Address))
   (where/error Unboxed-value_new (replace-field Unboxed-value_old f Value_new))
   ]

  )

(define-metafunction Dada
  ;; logical-write-traversal
  ;;
  ;; Creates the actions to write to Traversal without actually changing anything
  ;; in the heap. Used when lending the location.
  logical-write-traversal : Store Traversal -> (Fallible-actions Box-value)

  [(logical-write-traversal Store (Traversal-origin = Box-value))
   (swap-traversal Store (Traversal-origin = Box-value) Box-value)
   ]

  )

(define-metafunction Dada
  replace-field : Unboxed-value f Value -> Unboxed-value

  [(replace-field Unboxed-value f Value)
   (Aggregate-id (Field-value_0 ... (f Value) Field-value_1 ...))
   (where/error (Aggregate-id (Field-value_0 ... (f Value_old) Field-value_1 ...)) Unboxed-value)]
  )

(define-metafunction Dada
  write-traversal-origin : Store Traversal-origin -> Fallible-actions

  [; modify local variable: no perms needed
   (write-traversal-origin Store x)
   ()]

  [; attempt to modify shared field: error
   (write-traversal-origin Store (Traversal f shared))
   (expired)]

  [; attempt to modify var field with non-unique permission: error
   (write-traversal-origin Store (Traversal f var))
   (expired)
   (where/error (Traversal-origin = (Permission box Address)) Traversal)
   (where #f (unique-permission? Permission))
   ]

  [; attempt to modify var field with unique permission: requires context be mutable, too
   (write-traversal-origin Store (Traversal f var))
   (Fallible-action ... (write-address Permission Address))
   (where/error (Traversal-origin = (Permission box Address)) Traversal)
   (where #t (unique-permission? Permission))
   (where (Fallible-action ...) (write-traversal-origin Store Traversal-origin))
   ]

  [; attempt to modify atomic field: field needs to be readable
   (write-traversal-origin Store (Traversal f atomic))
   (read-traversal-origin Store (Traversal f atomic))
   ]

  )

(define-metafunction Dada
  unique-permission? : Permission -> boolean

  [(unique-permission? my) #t]
  [(unique-permission? (lent _)) #t]
  [(unique-permission? (shared _)) #f]
  [(unique-permission? our) #f]
  )

(define-metafunction Dada
  owned-permission? : Permission -> boolean

  [(owned-permission? my) #t]
  [(owned-permission? our) #t]
  [(owned-permission? (lent _)) #f]
  [(owned-permission? (shared _)) #f]
  )

(define-metafunction Dada
  traversal-address : Traversal -> Address

  [(traversal-address (_ = (_ box Address))) Address]
  )

(define-metafunction Dada
  read-traversal : Store Traversal -> (Fallible-actions Box-value)

  [(read-traversal Store Traversal)
   (Fallible-actions Box-value)
   (where/error (Traversal-origin = Box-value) Traversal)
   (where/error Fallible-actions (read-traversal-origin Store Traversal-origin))
   ]
  )

(define-metafunction Dada
  read-traversal-origin : Store Traversal-origin -> Fallible-actions

  [; read local variable: no perms needed
   (read-traversal-origin Store x)
   ()]

  [; attempt to read field of any kind
   (read-traversal-origin Store (Traversal f _))
   (Fallible-action ... (read-address Permission Address))
   (where/error (Traversal-origin = (Permission box Address)) Traversal)
   (where (Fallible-action ...) (read-traversal-origin Store Traversal-origin))
   ]

  )

(module+ test
  (redex-let*
   Dada
   [; corresponds roughly to the diagram at the top of this file, with some additions
    (Store (term (test-store
                  [(pair (my box a1))
                   (sh-p (my box a9))]
                  [(a1 (box 1 ((class Pair) ((a (my box a2)) (b (my box a3))))))
                   (a2 (box 1 ((class Point) ((x (our box a4)) (y (our box a5))))))
                   (a3 (box 1 ((class Point) ((x (my box a6)) (y (my box a7))))))
                   (a4 (box 2 22))
                   (a5 (box 2 44))
                   (a6 (box 1 66))
                   (a7 (box 1 88))
                   (a8 (box 1 99))
                   (a9 (box 1 ((class ShPoint) ((x (our box a4)) (y (our box a5))))))
                   ]
                  []
                  )))
    (Traversal_pair_a_x (term (traversal program_test Store (pair a x))))
    (Traversal_pair (term (traversal program_test Store (pair))))
    (Traversal_sh-p_x (term (traversal program_test Store (sh-p x))))
    ]

   (test-equal-terms Traversal_pair_a_x
                     (((((pair = (my box a1)) a var) = (my box a2)) x var)
                      =
                      (our box a4)))

   (; mutating var fields propagates through the path
    test-equal-terms (swap-traversal Store Traversal_pair_a_x (my box a8))
                     (((write-address my a1)
                       (write-address my a2)
                       (update-address
                        a2
                        ((class Point) ((x (my box a8)) (y (our box a5))))))
                      (our box a4)))

   (; mutate a local variable
    test-equal-terms (swap-traversal Store Traversal_pair (my box a8))
                     (((update-local pair (my box a8))) (my box a1)))

   (; can't mutate a shared field
    test-equal-terms (swap-traversal Store Traversal_sh-p_x (my box a8))
                     ((expired
                       (update-address
                        a9
                        ((class ShPoint) ((x (my box a8)) (y (our box a5))))))
                      (our box a4)))

   (; can read a shared field
    test-equal-terms (read-traversal Store Traversal_sh-p_x)
                     (((read-address my a9)) (our box a4)))
   )
  )
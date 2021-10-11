#lang racket

(require redex
         "../grammar.rkt"
         "../util.rkt"
         "lang.rkt"
         "stack.rkt"
         "heap.rkt"
         "test-store.rkt")

(provide traversal
         swap-traversal
         read-traversal)

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
  traversal : program Store place-at-rest -> Traversal or expired

  [(traversal program Store (x f ...))
   expired
   (where expired (var-in-store Store x))
   ]

  [(traversal program Store (x f ...))
   (traverse-fields program Store (x = Box-value) (f ...))
   (where Box-value (var-in-store Store x))
   ]

  )

(define-metafunction Dada
  traverse-fields : program Store Traversal (f ...) -> Traversal or expired

  [(traverse-fields program Store Traversal ())
   Traversal
   ]

  [(traverse-fields program Store Traversal (f_0 f_1 ...))
   expired
   (where (expired _) (field-from-traversal program Store Traversal f_0))
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
   (where/error (_ = (_ box Address)) Traversal)
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
  swap-traversal : Store Traversal Box-value -> (Fallible-actions Box-value)

  [; modify local variable: easy
   (swap-traversal Store (x = Box-value_old) Box-value_new)
   (((update-local x Box-value_new)) Box-value_old)
   ]

  [; attempt to modify shared field: error
   (swap-traversal Store ((Traversal f shared) = Box-value_old) Box-value_new)
   ((expired) Box-value_old)]

  [; attempt to modify var field: requires context be mutable
   (swap-traversal Store ((Traversal f var) = Box-value_old) Box-value_new)
   ((Fallible-action ... (update-address Address Unboxed-value_new)) Box-value_old)
   (where (Fallible-action ...) (write-traversal-origin Store (Traversal f var)))
   (where/error (_ = (_ box Address)) Traversal)
   (where/error Unboxed-value_old (load-heap Store Address))
   (where/error Unboxed-value_new (replace-field Unboxed-value_old f Box-value_new))
   ]

  )

(define-metafunction Dada
  replace-field : Unboxed-value f Box-value -> Unboxed-value

  [(replace-field Unboxed-value f Box-value)
   (Aggregate-id (Field-value_0 ... (f Box-value) Field-value_1 ...))
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

  ; FIXME: Atomic

  )

(define-metafunction Dada
  unique-permission? : Permission -> boolean

  [(unique-permission? my) #t]
  [(unique-permission? (lent _)) #t]
  [(unique-permission? (shared _)) #f]
  [(unique-permission? our) #f]
  )

(define-metafunction Dada
  read-traversal : Store Traversal -> (Fallible-actions Box-value)

  [(read-traversal Store Traversal)
   (Fallible-actions Box-value)
   (where/error Fallible-actions (read-traversal-contents Store Traversal))
   (where/error (_ = Box-value) Traversal)]
  )

(define-metafunction Dada
  read-traversal-contents : Store Traversal -> Fallible-actions

  [; read local variable: no perms needed
   (read-traversal-contents Store (x = Box-value_old))
   ()]

  [; attempt to read field of any kind
   (read-traversal-contents Store ((Traversal f _) = Box-value_old))
   (Fallible-action ... (read-address Permission Address))
   (where (Fallible-action ...) (read-traversal-contents Store Traversal))
   (where/error (_ = (Permission box Address)) Traversal)
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
                     ((expired) (our box a4)))

   (; can read a shared field
    test-equal-terms (read-traversal Store Traversal_sh-p_x)
                     (((read-address my a9)) (our box a4)))
   )
  )
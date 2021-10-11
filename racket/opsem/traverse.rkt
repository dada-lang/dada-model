#lang racket

(require redex
         "../grammar.rkt"
         "../util.rkt"
         "lang.rkt"
         "stack.rkt"
         "heap.rkt"
         "test-store.rkt")

(provide traversal)

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

(module+ test
  (redex-let*
   Dada
   [(; the Store encodes the diagram from the top of this file
     Store (term (test-store
                  [(pair (my box a1))]
                  [(a1 (box 1 ((class Pair) ((a (my box a2)) (b (my box a3))))))
                   (a2 (box 1 ((class Point) ((x (my box a4)) (y (my box a5))))))
                   (a3 (box 1 ((class Point) ((x (my box a6)) (y (my box a7))))))
                   (a4 (box 1 22))
                   (a5 (box 1 44))
                   (a6 (box 1 66))
                   (a7 (box 1 88))
                   ]
                  []
                  )))]
   (test-equal-terms (traversal program_test Store (pair a x))
                     (((((pair = (my box a1)) a var) = (my box a2)) x var)
                      =
                      (my box a4)))
   )
  )
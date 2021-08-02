#lang racket
(require redex "grammar.rkt" "util.rkt")
(require "type-system/lang.rkt" "type-system/initialization.rkt" "type-system/terminate-lease.rkt" "type-system/assignable.rkt"
         "type-system/lease-implication.rkt")
(provide (all-defined-out)
         (all-from-out "type-system/lang.rkt"))

;; expr-type env_in expr_in ty_out env_out
;;
;; Computes the type of an expression in a given environment,
;; as well as the resulting environment for subsequent expressions.
(define-judgment-form
  dada-type-system
  #:mode (expr-type I I I O O)
  #:contract (expr-type program env expr ty env)

  ;; Numbers always have type `int`.
  [--------------------------
   (expr-type _ env_in number int env_in)]

  ;; Empty sequences have int type.
  [--------------------------
   (expr-type _ env_in (seq) int env_in)]

  ;; Sequences thread the environment through each expr,
  ;; and they discard intermediate values. Their type is
  ;; the type of the final value.
  [(expr-type program env_in (seq expr_0 ...) ty_mid env_mid)
   (expr-type program env_mid expr_last ty_last env_last)
   --------------------------
   (expr-type program env_in (seq expr_0 ... expr_last) ty_last env_last)]

  [; First type the initializer
   (expr-type program env_in expr_init ty_init env_init)

   ; For simplicity, an error to shadow variables
   (side-condition (term (not (env-contains-var env_init x))))

   ; The initializer must be assignable to `ty`
   (ty-assignable program ty_init ty_x)
   
   ; Introduce `x: ty_x` into the environment
   (where env_last (env-with-var env_init x ty_x)) 
   --------------------------
   (expr-type program env_in (let (x ty_x) = expr_init) int env_last)]

  ;; Sharing a place:
  ;;
  ;; * Sharing qualifies as a read.
  ;; * The data must be "definitely-initialized".
  ;; * If we are sharing something that is already shared,
  ;;   then the resulting type doesn't change, and hence
  ;;   the reusting value is independent of `place`.
  ;; * But if we are sharing something owned, then we
  ;;   get back a `(shared place)` lease.
  [(side-condition (definitely-initialized env_in place))
   (where leases ((shared place)))
   (where ty_place (place-ty program env_in place))
   (where ty_shared (share-ty program leases ty_place))
   (where env_out (terminate-lease program env_in read place))
   --------------------------
   (expr-type program env_in (share place) ty_shared env_out)]

  )

(redex-let*
 dada-type-system
 [(program program_test)
  (env_empty env_empty)
  ]

 (test-equal-terms lease_x lease_x)
 )
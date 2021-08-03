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

  ;; number
  ;;
  ;; Numbers always have type `int`.
  [--------------------------
   (expr-type _ env_in number int env_in)]

  ;; (seq exprs)
  ;;
  ;; Sequences thread the environment through each expr,
  ;; and they discard intermediate values. Their type is
  ;; the type of the final value.
  [(exprs-types program env_in (expr_0 ... expr_n) (ty_0 ... ty_n) env_out)
   --------------------------
   (expr-type program env_in (seq (expr_0 ... expr_n)) ty_n env_out)]

  ;; As a special case, empty sequences evaluate to 0.
  [--------------------------
   (expr-type program env_in (seq ()) int env_in)]

  ;; (let (x ty) = expr)
  ;;
  ;; Introduce a new variable into the environment.
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

  ;; (set place = expr_value)
  ;;
  ;; Overwrite place
  [(expr-type program env_in expr_value ty_value env_value)
   (ty-assignable program ty_value (place-type env_in place))
   (where env_out (terminate-lease program env_value write place))
   ; FIXME -- need to make `place` definitely initialized
   --------------------------
   (expr-type program env_in (set place = expr_value) int env_out)]

  ;; (share place)
  ;;
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

  ;; (data-instance dt params exprs)
  ;;
  ;; Evaluates to a data instance.
  [(where (data generic-decls ((f ty_f0) ...)) (datatype-named program dt))
   (where (ty_f1 ...) ( (subst-ty program generic-decls params ty_f0) ...))
   (exprs-types program env_in exprs_fields (ty_v ...) env_out)
   (ty-assignable program ty_v ty_f1) ...
   --------------------------
   (expr-type program env_in (data-instance dt params exprs_fields) (dt params) env_out)]

  ;; (class-instance c params exprs)
  ;;
  ;; Evaluates to a (owned) class instance.
  [(where (class generic-decls ((f ty_f0) ...)) (class-named program c))
   (where (ty_f1 ...) ((subst-ty program generic-decls params ty_f0) ...))
   (exprs-types program env_in exprs_fields (ty_v ...) env_out)
   (ty-assignable program ty_v ty_f1) ...
   --------------------------
   (expr-type program env_in (class-instance c params exprs_fields) (my c params) env_out)]

  )

;; Computes the types of a series of expressions,
;; threading the environment through from one to the next.
(define-judgment-form
  dada-type-system
  #:mode (exprs-types I I I O O)
  #:contract (exprs-types program env exprs tys env)

  [--------------------------
   (exprs-types program env () () env)]

  [(expr-type program env_in expr_0 ty_0 env_0)
   (exprs-types program env_0 (expr_1 ...) (ty_1 ...) env_1)
   --------------------------
   (exprs-types program env_in (expr_0 expr_1 ...) (ty_0 ty_1 ...) env_1)]
  )

(redex-let*
 dada-type-system
 [(program program_test)
  (env_empty env_empty)
  ]

 (test-equal-terms lease_x lease_x)
 
 (test-judgment-holds 
  (expr-type
   program
   env_empty
   (seq ())
   int
   env_empty))

 (test-judgment-holds 
  (expr-type
   program
   env_empty
   (data-instance Point () (22 44))
   (Point ())
   env_empty))
 )
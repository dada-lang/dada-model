#lang racket
(require redex
         "../grammar.rkt"
         "../util.rkt"
         "../type-manip.rkt")
(provide (all-defined-out))

(define-extended-language dada-type-system dada
  ;; State of a place P:
  ;;
  ;; * if P or some prefix of P is found in def-init, then definitely initialized
  ;; * if P or some prefix of P is found in maybe-init, then potentially init
  ;; * otherwise, value is known to be uninitialized
  ;;
  ;; If a value is maybe-init, then it is considered live
  ;; (it can still be dropped by a dead comment).
  ;;
  ;; The `(dead x)` command removes `P` from `var-tys` and all initialization.
  ;; At runtime, it runs any destructors and cleans up memory. At compilation time,
  ;; it is also used to simulate NLL -- e.g., running `(dead x)` signals that a
  ;; borrow `x` is completed.
  (env (maybe-inits def-inits env-vars))
  (maybe-inits (maybe-init places))
  (def-inits (def-init places))
  (env-vars (vars var-tys))
  (var-tys ((x ty) ...))
  (action-kind read write)
  (action (action-kind place))
  )

(define env_empty
  (term ((maybe-init ())
         (def-init ())
         (vars ()))))

(define-metafunction dada-type-system
  test-env : (x ty) ... -> env

  [(test-env) ,env_empty]
  [(test-env (x_0 ty_0) ... (x_1 ty_1))
   (env-with-var (test-env (x_0 ty_0) ...) x_1 ty_1)])

(define-metafunction dada-type-system
  env-equal? : env env -> boolean
  [(env-equal? env env) #t]
  [(env-equal? env_1 env_2) #f])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic accessors for maybe-init, definitely-initialized
;;
;; For extended reasoning, see "initialization.rkt"

(define-metafunction dada-type-system
  maybe-initialized-places : env -> places
  [(maybe-initialized-places ((maybe-init places) _ _)) places])

(define-metafunction dada-type-system
  definitely-initialized-places : env -> places
  [(definitely-initialized-places (_ (def-init places) _)) places])

(define-metafunction dada-type-system
  env-with-definitely-initialized-places : env places  -> env
  [(env-with-definitely-initialized-places (maybe-inits _ env-vars) places)
   (maybe-inits (def-init places) env-vars)])

(define-metafunction dada-type-system
  env-with-initialized-places : env places_def places_maybe  -> env
  [(env-with-initialized-places (_ _ env-vars) places_def places_maybe)
   ((maybe-init places_maybe) (def-init places_def) env-vars)])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Variable types

;; var-ty env x -> ty
;;
;; Find the type for `x` in the environment.
(define-metafunction dada-type-system
  var-ty : env x -> ty
  [(var-ty (_ _ (vars ((x_0 ty_0) ... (x ty) (x_1 ty_1) ...))) x) ty])

;; env-contains-var? env x -> boolean
;;
;; True if `env` defines the variable `x`.
(define-metafunction dada-type-system
  env-contains-var? : env x -> boolean
  [(env-contains-var? (_ _ (vars ((x_0 _) ... (x _) (x_1 _) ...))) x) #t]
  [(env-contains-var? (_ _ _) x) #f])

;; env-with-var env x ty -> env
;;
;; Extend an environment with a new variable `x: ty`. `x` must
;; not already have been present in the environment.
(define-metafunction dada-type-system
  env-with-var : env_in x_in ty -> env
  #:pre (not? (env-contains-var? env_in x_in))
  [(env-with-var env x ty)
   (maybe-inits def-inits (vars ((x ty) (x_env ty_env) ...)))
   (where (maybe-inits def-inits (vars ((x_env ty_env) ...))) env)
   ]
  )

(define-metafunction dada-type-system
  place-field-mutability : program env place f -> mutability

  [(place-field-mutability program env place f)
   (ty-field-mutability program (place-ty program env place) f)]
  )

;; place-ty program env place -> ty
;;
;; Computes the type of a place in the given environment;
(define-metafunction dada-type-system
  place-ty : program env place -> ty

  [(place-ty program env (x f ...))
   (fields-ty program (var-ty env x) f ...)])

(redex-let*
 dada-type-system
 [(program program_test)
  (ty_my_string (term (my String ())))
  (ty_vec_string (term (my Vec (ty_my_string))))
  (ty_fn_string_string (term (my Fn (ty_my_string ty_my_string))))
  (ty_cell_string (term (my Cell (ty_my_string))))
  (ty_option_string (term (Option (ty_my_string))))
  (ty_point (term (Point ())))
  (leases_ours (term ()))
  (mode_ours (term (shared leases_ours)))
  (ty_shared_string (term (mode_ours String ())))
  (ty_option_shared_string (term (Option (ty_shared_string))))
  (leases_x (term ((shared (x)))))
  (ty_some_shared_string (term (Some (ty_shared_string))))
  (ty_pair (term (my Pair (ty_my_string ty_some_shared_string)))) ; Pair<my String, Some<our String>>
  (env (term ((maybe-init ())
              (def-init ())
              (vars ((some-our-str ty_some_shared_string)
                     (pair ty_pair))))))
  ]

 ;; simple test for substitution
 (test-equal-terms (place-ty program env (some-our-str value)) ty_shared_string)

 ;; test longer paths, types with >1 parameter
 (test-equal-terms (place-ty program env (pair b value)) ty_shared_string)

 )
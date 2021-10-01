#lang racket
(require redex
         "../grammar.rkt"
         "../util.rkt")
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
  (env (maybe-inits def-inits env-vars atomic?))
  (maybe-inits (maybe-init places))
  (def-inits (def-init places))
  (env-vars (vars var-tys))
  (action-kind read write give store-in-flight)
  (action (action-kind place)
          noop
          drop-in-flight
          (gather ((x place) ...))
          (unscope-vars xs))
  )

(define-term env_empty
  ((maybe-init ())
   (def-init ())
   (vars ())
   ()))

(define-term env-empty
  ((maybe-init ())
   (def-init ())
   (vars ())
   ()))

(define-metafunction dada-type-system
  test-env : (x ty) ... -> env

  [(test-env) env_empty]
  [(test-env (x_0 ty_0) ... (x_1 ty_1))
   (env-with-initialized-var (test-env (x_0 ty_0) ...) x_1 ty_1)])

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
  [(maybe-initialized-places ((maybe-init places) _ _ _)) places])

(define-metafunction dada-type-system
  definitely-initialized-places : env -> places
  [(definitely-initialized-places (_ (def-init places) _ _)) places])

(define-metafunction dada-type-system
  env-with-definitely-initialized-places : env places  -> env
  [(env-with-definitely-initialized-places (maybe-inits _ env-vars atomic?) places)
   (maybe-inits (def-init places) env-vars atomic?)])

(define-metafunction dada-type-system
  env-with-initialized-places : env places_def places_maybe  -> env
  [(env-with-initialized-places (_ _ env-vars atomic?) places_def places_maybe)
   ((maybe-init places_maybe) (def-init places_def) env-vars atomic?)])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Variable types

(define-metafunction dada-type-system
  ;; var-ty-in-env env x -> ty
  ;;
  ;; Find the type for `x` in the environment.
  var-ty-in-env : env x -> ty
  [(var-ty-in-env (_ _ (vars ((x_0 ty_0) ... (x ty) (x_1 ty_1) ...)) _) x) ty])

(define-metafunction dada-type-system
  ;; env-vars env -> var-tys
  ;;
  ;; Returns the lits of defined variables, and their types, in the given environment.
  var-tys-in-env : env -> var-tys
  [(var-tys-in-env (_ _ (vars var-tys) _)) var-tys])

(define-metafunction dada-type-system
  ;; env-contains-var? env x -> boolean
  ;;
  ;; True if `env` defines the variable `x`.
  env-contains-var? : env x -> boolean
  [(env-contains-var? (_ _ (vars ((x_0 _) ... (x _) (x_1 _) ...)) _) x) #t]
  [(env-contains-var? _ x) #f])

(define-metafunction dada-type-system
  ;; env-with-var env (x ty) ... -> env
  ;;
  ;; Extend an environment with a new variable(s) `x: ty`. `x` must
  ;; not already have been present in the environment.
  env-with-var : env_in (x_in ty) ... -> env
  #:pre (not? (env-contains-var? env_in x_in) ...)
  [(env-with-var env (x ty) ....)
   (maybe-inits def-inits (vars ((x ty) ... (x_env ty_env) ...)) atomic?)
   (where (maybe-inits def-inits (vars ((x_env ty_env) ...)) atomic?) env)
   ]
  )

(define-metafunction dada-type-system
  ;; env-with-var-tys env var-tys -> env
  ;;
  ;; Returns the same environment with a new set of variable typings.
  env-with-var-tys : env var-tys -> env
  [(env-with-var-tys env var-tys)
   (maybe-inits def-inits (vars var-tys) atomic?)
   (where (maybe-inits def-inits _ atomic?) env)])

(define-metafunction dada-type-system
  ;; env-with-initialized-var env x ty -> env
  ;;
  ;; Extend an environment with a new variable `x: ty` and add it to the
  ;; list of initialized places. `x` must
  ;; not already have been present in the environment.
  env-with-initialized-var : env_in x_in ty -> env
  #:pre (not? (env-contains-var? env_in x_in))
  [(env-with-initialized-var env x ty)
   ((maybe-init (place_mi ... (x))) (def-init (place_di ... (x))) (vars ((x ty) (x_env ty_env) ...)) atomic?)
   (where ((maybe-init (place_mi ...)) (def-init (place_di ...)) (vars ((x_env ty_env) ...)) atomic?) env)
   ]
  )

(define-metafunction dada-type-system
  ;; env-with-initialized-vars env var-tys -> env
  env-with-initialized-vars : env_in var-tys -> env
  [(env-with-initialized-vars env ((x_0 ty_0) (x_1 ty_1) ...))
   (env-with-initialized-vars (env-with-initialized-var env x_0 ty_0) ((x_1 ty_1) ...))
   ]

  [(env-with-initialized-vars env ()) env]
  )

(define-metafunction dada-type-system
  ;; fresh-temporaries program env exprs xs -> xs
  ;;
  ;; Yields up a set of fresh temporary variables
  ;; that are do not appear in the program, environment,
  ;; or exprs. The names will be based on the names
  ;; in `xs`.
  fresh-temporaries : program env exprs ids -> ids

  [(fresh-temporaries program env exprs ids)
   ,(variables-not-in (term (program env exprs)) (term ids))]

  )

(define-metafunction dada-type-system
  ;; vars-added-to-env env_old env_new -> xs
  ;;
  ;; Returns all variables added to env_new that were not present in env_old
  vars-added-to-env : env_old env_new -> xs
  [(vars-added-to-env env_old env_new)
   ,(set-subtract (term (x_new ...) ) (term (x_old ...)))
   (where ((x_old _) ...) (var-tys-in-env env_old))
   (where ((x_new _) ...) (var-tys-in-env env_new))
   ]
  )

(define-metafunction dada-type-system
  ;; env-without-vars
  ;;
  ;; Removes the given variables from the lists of declared variables
  ;; and initialized places in `env`. *Does not adjust the types of
  ;; other variables, which may still reference `xs`!*
  ;; You must do that first with the `adjust-leases` functions
  ;; before invoking this function.
  env-without-vars : env xs -> env

  [(env-without-vars env xs)
   ((maybe-init places_maybe-init) (def-init places_def-init) (vars var-tys) atomic?)
   (where var-tys (var-tys-without-vars (var-tys-in-env env) xs))
   (where places_def-init (places-without-vars (definitely-initialized-places env) xs))
   (where places_maybe-init (places-without-vars (maybe-initialized-places env) xs))
   (where atomic? (env-atomic env))
   ]
  )

(define-metafunction dada-type-system
  ;; var-tys-without-vars
  ;;
  ;; Helper for env-without-vars
  var-tys-without-vars : var-tys xs -> var-tys

  [(var-tys-without-vars () xs) ()]

  [(var-tys-without-vars ((x _) var-ty ...) xs)
   (var-tys-without-vars (var-ty ...) xs)
   (where (_ ... x _ ...) xs)]

  [(var-tys-without-vars ((x ty) var-ty ...) xs)
   ((x ty) var-ty_1 ...)
   (where/error (var-ty_1 ...) (var-tys-without-vars (var-ty ...) xs))
   ]

  )

(define-metafunction dada-type-system
  ;; places-without-vars
  ;;
  ;; Helper for env-without-vars
  places-without-vars : places xs -> places

  [(places-without-vars () xs) ()]

  [(places-without-vars ((x f ...) place ...) xs)
   (places-without-vars (place ...) xs)
   (where (_ ... x _ ...) xs)]

  [(places-without-vars (place_0 place_1 ...) xs)
   (place_0 place_2 ...)
   (where/error (place_2 ...) (places-without-vars (place_1 ...) xs))
   ]

  )

(define-metafunction dada-type-system
  joint-perms? : env perms -> boolean
  [(joint-perms? env our) #t]
  [(joint-perms? env (shared _)) #t]
  [(joint-perms? env my) #f]
  [(joint-perms? env (lent _)) #f]
  )

(define-metafunction dada-type-system
  unique-perms? : env perms -> boolean
  [(unique-perms? env perms) (not? (joint-perms? env perms))])

(module+ test
  (redex-let*
   dada-type-system
   [(env (term (test-env)))
    (exprs (term (22 44)))
    (ids (term (x y)))
    ]

   (test-equal-terms (fresh-temporaries program_test env exprs ids) (x1 y1))
   )

  (test-equal-terms (vars-added-to-env (test-env (x int) (z int))
                                       (test-env (w int) (x int) (y int) (z int)))
                    (w y))

  (test-equal-terms (env-without-vars (test-env (w int) (x int) (y int) (z int)) (w y))
                    (test-env (x int) (z int)))
  )


;;;;;;;;;;;;;;;;;;;;;;;;
;; Atomic

(define-metafunction dada-type-system
  ;; env-atomic env -> atomic?
  ;;
  ;; Find the type for `x` in the environment.
  env-atomic : env -> atomic?
  [(env-atomic (_ _ _ atomic?)) atomic?]
  )

(define-metafunction dada-type-system
  ;; env-atomic env -> atomic?
  ;;
  ;; Find the type for `x` in the environment.
  env-with-atomic : env atomic? -> env
  [(env-with-atomic (maybe-inits def-inits env-vars _) atomic?)
   (maybe-inits def-inits env-vars atomic?)]
  )

;;;;;;;;;;;;;;;;;;;;;;;;
;; Place typing etc


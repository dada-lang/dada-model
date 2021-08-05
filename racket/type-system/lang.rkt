#lang racket
(require redex "../grammar.rkt" "../util.rkt")
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
  ;; The `(dead x)` command removes `P` from `var-types` and all initialization.
  ;; At runtime, it runs any destructors and cleans up memory. At compilation time,
  ;; it is also used to simulate NLL -- e.g., running `(dead x)` signals that a
  ;; borrow `x` is completed.
  (env (maybe-inits def-inits env-vars))
  (maybe-inits (maybe-init places))
  (def-inits (def-init places))
  (env-vars (vars var-types))
  (var-types ((x ty) ...))
  (action-kind read write)
  (action (action-kind place))
  )

(define env_empty
  (term ((maybe-init ())
         (def-init ())
         (vars ()))))
 
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

;; var-type env x -> ty
;;
;; Find the type for `x` in the environment.
(define-metafunction dada-type-system
  var-type : env x -> ty
  [(var-type (_ _ (vars ((x_0 ty_0) ... (x ty) (x_1 ty_1) ...))) x) ty])

;; env-contains-var env x -> boolean
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Type manipulation

;; subst-ty program generic-decls params ty -> ty
;;
;; Given some `ty` that appeared inside an item
;; with the generics `generic-decls`, substitute the
;; values `params`.
(define-metafunction dada-type-system
  subst-ty : program generic-decls params ty -> ty

  ; Optimization: no parameters? identity
  [(subst-ty program () () ty) ty]
  
  ; Interesting case: when we find a parameter `(mode p)`:
  ; * Find the corresponding type `ty_p` from the params list
  ; * Apply the mode `mode` to `ty_p`
  [(subst-ty program (generic-decl ...) (param ...) (mode p))
   (apply-mode program mode ty_p)
   (where ((generic-decl_0 param_0) ... ((p _) ty_p) (generic-decl_1 param_1) ...) ((generic-decl param) ...))
   ]

  [(subst-ty program generic-decls params int) int]
  [(subst-ty program generic-decls params (dt (param ...)))
   (dt ((subst-param program generic-decls params param) ...))]
  [(subst-ty program generic-decls params (mode c (param ...)))
   (mode c ((subst-param program generic-decls params param) ...))]
  [(subst-ty program generic-decls params (mode borrowed (lease ...) ty))
   (mode borrowed
         ((subst-lease program generic-decls lease) ...)
         (subst-ty program generic-decls params ty))]
  
  )

(define-metafunction dada-type-system
  subst-lease : program generic-decls params lease -> lease
  
  ; Interesting case: when we find a parameter `p`, replace
  ; it with value from parameter list.
  [(subst-lease program (generic-decl ...) (param ...) p)
   lease_p
   (where ((generic-decl_0 param_1) ... ((p _) lease_p) (generic-decl_1 param_1) ...) ((generic-decl param) ...))
   ]

  [(subst-lease program generic-decls params (lease-kind place))
   (lease-kind place)]

  )

(define-metafunction dada-type-system
  subst-param : program generic-decls params param -> param
  
  [(subst-param program generic-decls params ty)
   (subst-ty program generic-decls params ty)]

  [(subst-param program generic-decls params lease)
   (subst-lease program generic-decls params lease)]
  
  )

;; merge-leases leases ...
;;
;; Combines some number of leases into one set.
;; The resulting set is in a canonical order, but you
;; cannot in general assume that equivalent sets
;; will be equal. For example:
;;
;; * we don't currently remove leases that are implied by other
;;   other leases (e.g., `(shared (x))` => `(shared (x y))`, but
;;   we will keep both of them.
;; * even if we did, `(shared (x y))` and `(shared (x))`
;;   could be equivalent if `x` has only one field, `y`.
(define-metafunction dada-type-system
  merge-leases : leases ... -> leases

  [(merge-leases leases ...)
   ,(sort (remove-duplicates (append* (term (leases ...)))) place<?)])

;; place-type program env place -> ty
;;
;; Computes the type of a place in the given environment;
(define-metafunction dada-type-system
  place-type : program env place -> ty

  [(place-type program env (x f ...))
   (field-types program env (var-type env x) f ...)])

;; field-types program env ty f ...
;;
;; Given an owner type `ty` and a list of fields,
;; computes the final type.
(define-metafunction dada-type-system
  field-types : program env ty f ... -> ty

  [(field-types program env ty) ty]
  [(field-types program env ty f_0 f_1 ...)
   (field-types program env ty_0 f_1 ...)
   (where ty_0 (field-type program env ty f_0))])

;; field-type program env ty f -> ty
;;
;; Compute the type of a field `f` within an
;; owner of type `ty`.
(define-metafunction dada-type-system
  field-type : program env ty f -> ty

  [(field-type program env (mode c params) f)
   (apply-mode program mode ty_f)
   (where ty_f_raw (class-field-ty program c f))
   (where generic-decls (class-generic-decls program c))
   (where ty_f (subst-ty program generic-decls params ty_f_raw))
   ]

  [(field-type program env (dt params) f)
   ty_f
   (where ty_f_raw (datatype-field-ty program dt f))
   (where generic-decls (datatype-generic-decls program dt))
   (where ty_f (subst-ty program generic-decls params ty_f_raw))]
  )

;; apply-mode program mode ty
;;
;; Given the mode on a field owner, apply that mode to the type of
;; the field. Also used in other contexts.
(define-metafunction dada-type-system
  apply-mode : program mode ty -> ty

  [(apply-mode program my ty) ty]
  [(apply-mode program (shared leases) ty) (share-ty program leases ty)]
  )

;; share-ty program leases ty
;;
;; Transform a type by sharing it.
(define-metafunction dada-type-system
  share-ty : program leases ty -> ty

  ;; "my" class becomes shared
  [(share-ty program leases (my c (param ...)))
   ((shared leases) c params_shared)
   (where (variance ...) (class-variances program c))
   (where params_shared ((share-param program leases variance param) ...))
   ]

  ;; shared classes don't change
  [(share-ty program leases ty)
   ty
   (where ((shared _) c _) ty)]

  ;; data types don't change, but their parameters might
  [(share-ty program leases int)
   int]
  [(share-ty program leases (dt (param ...)))
   (dt params_shared)
   (where (variance ...) (datatype-variances program dt))
   (where params_shared ((share-param program leases variance param) ...))]

  ;; generic types just alter their mode (further changes may result
  ;; after substitution)
  [(share-ty program leases (mode_p p))
   (mode_shared p)
   (where mode_shared (share-mode program leases mode_p))]

  ;; borrowed types
  [(share-ty program leases (mode_b borrowed leases_b ty_b))
   (mode_shared borrowed leases_b ty_b)
   (where mode_shared (share-mode program leases mode_b))]
  )

;; share-mode program leases mode -> mode
;;
;; Adjust mode to account for being shared for `leases`.
(define-metafunction dada-type-system
  share-mode : program leases mode -> mode

  [(share-mode program leases my) (shared leases)]
  [(share-mode program leases (shared leases_sh)) (shared leases_sh)])

;; share-param program leases variance param -> mode
;;
;; Adjust the value `param` of a generic parameter which
;; has variance `variance` to account for being shared
;; for `leases`.
(define-metafunction dada-type-system
  share-param : program leases variance param -> param

  [(share-param program leases out ty) (share-ty program leases ty)]
  [(share-param program leases _ param) param]
  )

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

 ;; sharing a class affects mode *and* propagates to out parameters
 (test-equal-terms (share-ty program leases_ours ty_my_string) ty_shared_string)
 (test-equal-terms (share-ty program leases_ours ty_vec_string) ((shared ()) Vec (((shared ()) String ()))))

 ;; ...but not in or inout parameters
 (test-equal-terms (share-ty program leases_ours ty_fn_string_string) (mode_ours Fn (ty_my_string ty_shared_string)))
 (test-equal-terms (share-ty program leases_ours ty_cell_string) (mode_ours Cell (ty_my_string)))

 ;; sharing a datatype propagates to (out) parameters, but nothing else
 (test-equal-terms (share-ty program leases_ours ty_option_string) ty_option_shared_string)
 (test-equal-terms (share-ty program leases_ours ty_point) ty_point)

 ;; sharing something shared: no effect
 (test-equal-terms (share-ty program leases_x ty_shared_string) ty_shared_string)

 ;; simple test for substitution
 (test-equal-terms (place-type program env (some-our-str value)) ty_shared_string)

 ;; test longer paths, types with >1 parameter
 (test-equal-terms (place-type program env (pair b value)) ty_shared_string)
)

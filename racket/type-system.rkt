#lang racket
(require redex "grammar.rkt" "util.rkt")
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
  (env ((maybe-init places) (def-init places) (vars var-types)))
  (var-types ((x ty) ...))
  )

(define-metafunction dada-type-system
  maybe-initialized-places : env -> places
  [(maybe-initialized-places ((maybe-init places) _ _)) places])

(define-metafunction dada-type-system
  definitely-initialized-places : env -> places
  [(definitely-initialized-places (_ (def-init places) _)) places])

(define-metafunction dada-type-system
  with-definitely-initialized-places : places env -> places
  [(with-definitely-initialized-places ((maybe-init places_m) _ (vars var-types)))
   ((maybe-init places_m) (def-init places) (vars var-types))])

(define-metafunction dada-type-system
  var-type : env x -> ty
  [(var-type (_ _ (vars var-types))) ,(cadr (assoc (term x) (term var-types)))])

;; subst-ty program generic-decls params ty -> ty
;;
;; Given some `ty` that appeared inside an item
;; with the generics `generic-decls`, substitute the
;; values `params`.
(define-metafunction dada-type-system
  subst-ty : program generic-decls params ty -> ty
  [(subst-ty program () () ty) ty])

;; definitely-initialized env place -> boolean
;;
;; True if place is definitely initialized
(define-metafunction dada-type-system
  definitely-initialized : env place -> boolean
  [(definitely-initialized env place)
   (place-or-prefix-in place (definitely-initialized-places env))])

;; maybe-initialized env place -> boolean
;;
;; True if place may be initialized
(define-metafunction dada-type-system
  maybe-initialized : env place -> boolean
  [(maybe-initialized env place)
   (place-or-prefix-in place (maybe-initialized-places env))])

;; definitely-not-initialized env place -> boolean
;;
;; True if place is definitely initialized
(define-metafunction dada-type-system
  definitely-not-initialized : env place -> boolean
  [(definitely-not-initialized env place)
   ,(not (term (place-or-prefix-in place (maybe-initialized-places env))))])

(redex-let*
 dada-type-system
 [(env (term ((maybe-init ((x) (y f) (y g)))
              (def-init ((x) (y f)))
              (vars ()))))]
 (test-equal (term (definitely-initialized env (x))) #t)
 (test-equal (term (definitely-initialized env (z))) #f)
 (test-equal (term (definitely-initialized env (y f))) #t)
 (test-equal (term (definitely-initialized env (y f f1))) #t)
 (test-equal (term (definitely-initialized env (y g))) #f)
 (test-equal (term (maybe-initialized env (y f g))) #t)
 (test-equal (term (maybe-initialized env (y g h))) #t)
 (test-equal (term (maybe-initialized env (y h))) #f)
 (test-equal (term (definitely-not-initialized env (y h))) #t)
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
 [(program (term ([(String (class () ()))
                   (Vec (class ((E out)) ()))
                   (Fn (class ((A in) (R out)) ()))
                   (Cell (class ((T inout)) ()))
                   ]
                  [(Point (data () ()))
                   (Option (data ((T out)) ()))
                   ]
                  [])))
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
 )

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
   (apply-mode-to-ty mode ty_f)
   (where ty_f_raw (class-field-type program c f))
   (where generic-decls (class-generic-decls c))
   (where ty_f (subst-ty program generic-decls params ty_f_raw))]

  [(field-type program env (dt params) f)
   ty_f
   (where ty_f_raw (datatype-field-type program dt f))
   (where generic-decls (datatype-generic-decls dt))
   (where ty_f (subst-ty program generic-decls params ty_f_raw))]
  )

;; terminate-leave program env lease-kind place -> env
;;
;; Removes any places from the list of "definitely initialized"
;; places whose types may reference (lease-kind place).
;;
;; This is used after place is accessed, and the lease-kind
;; is the kind of lease that is invalidated by that access.
;; So, for example, if we have a read of `x`, then we would
;; remove all places that have a type like that references
;; `borrowed x`.
;;
;; Note that these places remain in the 'maybe initialized'
;; list, which permits them to be dropped. This is ok because
;; dropping something of "shared/borrowed" mode has no effect.
;;
;; FIXME: For now, we just remove the entire place from
;; being considered initialized. At some point we might replace
;; it with more refined paths that are unaffected.
(define-metafunction dada-type-system
  terminate-lease : program env lease-kind place -> env

  [(terminate-lease program env lease-kind place)
   (with-definitely-initialized-places places env)
   (where places_def_init (definitely-initialized-places env))
   (where places ,(filter (λ (place) (term (place-references-lease program env ,place lease))) (term places_def_init)))
   ]
  )

(define-metafunction dada-type-system
  place-references-lease : program env place lease -> env

  [(place-references-lease program env place lease)
   (ty-references-lease program env ty lease)
   (where ty (place-type program env place))]
  )

(define-metafunction dada-type-system
  ty-references-lease : program env ty lease -> env

  [(ty-references-lease program env int _) #f]

  [(ty-references-lease program env (mode borrowed leases ty))
   (any (mode-references-lease program env mode lease)
        (leases-reference-lease program env leases lease)
        (ty-references-lease program env ty))]

  [(ty-references-lease program env (mode c params))
   (any (mode-references-lease program env mode lease)
        (params-reference-lease program env params lease))]

  [(ty-references-lease program env (mode p))
   (mode-references-lease program env mode lease)]
  
  [(ty-references-lease program env (dt params))
   (params-reference-lease program env mode lease)]
        
  )

(define-metafunction dada-type-system
  mode-references-lease : program env mode lease -> env

  [(mode-references-lease program env my _) #f]
  [(mode-references-lease program env (shared leases) lease)
   (leases-reference-lease program env leases lease)])

(define-metafunction dada-type-system
  params-reference-lease : program env params lease -> env

  [(params-reference-lease program env (param ...) lease)
   (any (param-references-lease program env param lease) ...)])

(define-metafunction dada-type-system
  param-references-lease : program env param lease -> env

  [(param-references-lease program env ty lease) (ty-references-lease program env ty lease)]
  [(param-references-lease program env leases lease) (leases-reference-lease program env ty lease)])

(define-metafunction dada-type-system
  leases-reference-lease : program env param lease -> env

  [(leases-reference-lease program env (lease_1 ...) lease_0)
   (any (lease-references-lease program env lease_1 lease_0) ...)])

;; lease-references-lease lease_1 lease_2
;;
;; True if revoking `lease_2` means `lease_1` is revoked.
(define-metafunction dada
  lease-references-lease : program env lease lease -> boolean

  ;; Examples:
  ;;
  ;; If we have a borrowed lease on `a.b`, and the user reads `a.b.c`, then our borrowed lease is revoked.
  ;; If we have a borrowed lease on `a.b.c`, and the user reads `a.b`, then our borrowed lease is revoked.
  ;; If we have a borrowed lease on `a.b.c`, and the user reads `a.d`, then our borrowed lease is unaffected.
  [(lease-references-lease (borrowed place_1) (shared place_2)) (places-overlapping place_1 place_2)]
  
  ;; If we have a shared/borrowed lease on `a.b`, and the user writes to `a.b.c`, then our shared lease is revoked.
  ;; If we have a shared/borrowed lease on `a.b.c`, and the user writes to `a.b`, then our shared lease is revoked.
  [(lease-references-lease (_ place_1) (borrowed place_2)) (places-overlapping place_1 place_2)]

  ;; If we have a shared lease on `a.b`, and the user reads some memory (no matter what), our lease is unaffected.
  [(lease-references-lease (shared place_1) (shared place_2)) #f]
  )

(redex-let*
 dada-type-system
 [(program (term ([(String (class () ()))
                   (Vec (class ((E out)) ()))
                   (Fn (class ((A in) (R out)) ()))
                   (Cell (class ((T inout)) ()))
                   ]
                  [(Point (data () ()))
                   (Option (data ((T out)) ()))
                   ]
                  [])))
  (env (term ((maybe-init ((x) (y f) (y g)))
                  (def-init ((x) (y f)))
                  (vars ()))))]
 (test-equal-terms (terminate-lease program env shared (x f)) ())
 )

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

  ;; Sharing a place
  [(side-condition (can-share env_in place))
   (side-condition (definitely-initialized env_in place))
   (where leases ((shared place)))
   (where ty_place (place-ty program env_in place))
   (where ty_shared (share-ty program leases ty_place))
   --------------------------
   (expr-type program env_in (share place) ty_shared env_in)]


  )
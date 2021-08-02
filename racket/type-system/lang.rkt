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
  (env ((maybe-init places) (def-init places) (vars var-types)))
  (var-types ((x ty) ...))
  (action-kind read write)
  (action (action-kind place))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic accessors for the env

(define-metafunction dada-type-system
  maybe-initialized-places : env -> places
  [(maybe-initialized-places ((maybe-init places) _ _)) places])

(define-metafunction dada-type-system
  definitely-initialized-places : env -> places
  [(definitely-initialized-places (_ (def-init places) _)) places])

(define-metafunction dada-type-system
  with-definitely-initialized-places : places env -> env
  [(with-definitely-initialized-places places ((maybe-init places_m) _ (vars var-types)))
   ((maybe-init places_m) (def-init places) (vars var-types))])

(define-metafunction dada-type-system
  var-type : env x -> ty
  [(var-type (_ _ (vars ((x_0 ty_0) ... (x ty) (x_1 ty_1) ...))) x) ty])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Type manipulation

;; subst-ty program generic-decls params ty -> ty
;;
;; Given some `ty` that appeared inside an item
;; with the generics `generic-decls`, substitute the
;; values `params`.
(define-metafunction dada-type-system
  subst-ty : program generic-decls params ty -> ty
  [(subst-ty program () () ty) ty])


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

#lang racket
(require redex data/order "grammar.rkt" "util.rkt")
(provide subst-ty
         fields-ty
         is-affine-ty
         is-copy-ty
         share-ty
         )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Type manipulation

(define-metafunction dada
  ;; subst-ty program generic-decls params ty -> ty
  ;;
  ;; Given some `ty` that appeared inside an item
  ;; with the generics `generic-decls`, substitute the
  ;; values `params`.
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

(define-metafunction dada
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

(define-metafunction dada
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
(define-metafunction dada
  merge-leases : leases ... -> leases

  [(merge-leases leases ...)
   ,(sort (remove-duplicates (append* (term (leases ...)))) place<?)])

(define-metafunction dada
  ;; apply-mode program mode ty
  ;;
  ;; Given the mode on a field owner, apply that mode to the type of
  ;; the field. Also used in other contexts.
  apply-mode : program mode ty -> ty

  [(apply-mode program my ty) ty]
  [(apply-mode program (shared leases) ty) (share-ty program leases ty)]
  )

(define-metafunction dada
  ;; share-ty program leases ty
  ;;
  ;; Transform a type by sharing it.
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

(define-metafunction dada
  ;; share-mode program leases mode -> mode
  ;;
  ;; Adjust mode to account for being shared for `leases`.
  share-mode : program leases mode -> mode

  [(share-mode program leases my) (shared leases)]
  [(share-mode program leases (shared leases_sh)) (shared leases_sh)])

(define-metafunction dada
  ;; share-param program leases variance param -> mode
  ;;
  ;; Adjust the value `param` of a generic parameter which
  ;; has variance `variance` to account for being shared
  ;; for `leases`.
  share-param : program leases variance param -> param

  [(share-param program leases out ty) (share-ty program leases ty)]
  [(share-param program leases _ param) param]
  )

(define-metafunction dada
  ;; fields-ty program env ty f ...
  ;;
  ;; Given an owner type `ty` and a list of fields,
  ;; computes the final type.
  fields-ty : program ty f ... -> ty

  [(fields-ty program ty) ty]
  
  [(fields-ty program ty f_0 f_1 ...)
   (fields-ty program ty_0 f_1 ...)
   (where ty_0 (field-ty program ty f_0))])

(define-metafunction dada
  ;; field-ty program env ty f -> ty
  ;;
  ;; Compute the type of a field `f` within an
  ;; owner of type `ty`.
  field-ty : program ty f -> ty

  [(field-ty program (mode c params) f)
   (apply-mode program mode ty_f)
   (where ty_f_raw (class-field-ty program c f))
   (where generic-decls (class-generic-decls program c))
   (where ty_f (subst-ty program generic-decls params ty_f_raw))
   (where #t (class-field-non-atomic? program c f))
   ]

  ; For atomic fields, the type ignores the mode of the
  ; owner.
  [(field-ty program (mode c params) f)
   (subst-ty program generic-decls params ty_f_raw)
   (where ty_f_raw (class-field-ty program c f))
   (where generic-decls (class-generic-decls program c))
   (where #t (class-field-atomic? program c f))
   ]

  [(field-ty program (dt params) f)
   ty_f
   (where ty_f_raw (datatype-field-ty program dt f))
   (where generic-decls (datatype-generic-decls program dt))
   (where ty_f (subst-ty program generic-decls params ty_f_raw))]

  [(field-ty program (dt params) f)
   ty_f
   (where ty_f_raw (datatype-field-ty program dt f))
   (where generic-decls (datatype-generic-decls program dt))
   (where ty_f (subst-ty program generic-decls params ty_f_raw))]

  [(field-ty program (_ borrowed _ ty) f)
   (field-ty program ty f)]
  )

(define-judgment-form dada
  #:mode (is-affine-ty I)
  #:contract (is-affine-ty ty)

  [--------------------------
   (is-affine-ty (my c _))]

  [--------------------------
   (is-affine-ty (my borrowed _ _))]

  [--------------------------
   (is-affine-ty (my p))]

  [(has-affine-param params)
   --------------------------
   (is-affine-ty (dt params))]
  )

(define-judgment-form dada
  #:mode (has-affine-param I)
  #:contract (has-affine-param params)

  [(is-affine-ty ty)
   --------------------------
   (has-affine-param (param_0 ... ty param_2 ...))]
  )

(define-judgment-form dada
  #:mode (is-copy-ty I)
  #:contract (is-copy-ty ty)

  [--------------------------
   (is-copy-ty int)]
  
  [--------------------------
   (is-copy-ty ((shared _) c _))]

  [--------------------------
   (is-copy-ty ((shared _) borrowed _ _))]

  [--------------------------
   (is-copy-ty ((shared _) p))]

  [(is-copy-param param) ...
   --------------------------
   (is-copy-ty (dt (param ...)))]
  )

(define-judgment-form dada
  #:mode (is-copy-param I)
  #:contract (is-copy-param param)

  [(is-copy-ty ty)
   --------------------------
   (is-copy-param ty)]

  [--------------------------
   (is-copy-param leases)]
  )

(module+ test
  (redex-let*
   dada
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

   (test-judgment-holds (is-affine-ty ty_option_string))
   (test-judgment-false (is-affine-ty ty_shared_string))
   )
  )
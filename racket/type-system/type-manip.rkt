#lang racket
(require redex
         data/order
         "../grammar.rkt"
         "../util.rkt"
         "lang.rkt"
         "share-ty.rkt")
(provide subst-ty
         fields-ty
         place-ty
         place-field-mutability
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

  [; Optimization: no parameters? identity
   (subst-ty program () () ty) ty]
  
  [; Interesting case: when we find a parameter `(mode p)`:
   ; * Find the corresponding type `ty_p` from the params list
   ; * Apply the mode `mode` to `ty_p`
   (subst-ty program (generic-decl ...) (param ...) (mode p))
   (apply-mode program mode ty_p)
   (where ((generic-decl_0 param_0) ... ((p _) ty_p) (generic-decl_1 param_1) ...) ((generic-decl param) ...))
   ]

  ; Uninteresting cases: propagate the substitution downwards
  
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
  
  [; Interesting case: when we find a parameter `p`, replace
   ; it with value from parameter list.
   (subst-lease program (generic-decl ...) (param ...) p)
   lease_p
   (where ((generic-decl_0 param_1) ... ((p _) lease_p) (generic-decl_1 param_1) ...) ((generic-decl param) ...))
   ]

  [; Otherwise, identity
   (subst-lease program generic-decls params (lease-kind place))
   (lease-kind place)]

  )

(define-metafunction dada
  subst-param : program generic-decls params param -> param
  
  [(subst-param program generic-decls params ty)
   (subst-ty program generic-decls params ty)]

  [(subst-param program generic-decls params lease)
   (subst-lease program generic-decls params lease)]
  
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

(define-metafunction dada-type-system
  ;; place-ty program env place -> ty
  ;;
  ;; Computes the type of a place in the given environment;
  place-ty : program env place-at-rest -> ty

  [(place-ty program env (x f ...))
   (fields-ty program (var-ty-in-env env x) f ...)])

(define-metafunction dada-type-system
  place-field-mutability : program env place f -> mutability

  [(place-field-mutability program env place f)
   (ty-field-mutability program (place-ty program env place) f)]
  )

(module+ test
  (redex-let*
   dada-type-system
   [(ty_my_string (term (my String ())))
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
                       (pair ty_pair)))
                ())))
    ]

   ;; simple test for substitution
   (test-equal-terms (place-ty program_test env (some-our-str value)) ty_shared_string)

   ;; test longer paths, types with >1 parameter
   (test-equal-terms (place-ty program_test env (pair b value)) ty_shared_string)

   )
  )
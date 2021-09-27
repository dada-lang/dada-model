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
         subst-vars-in-ty
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
   ((subst-mode program generic-decls params mode) c ((subst-param program generic-decls params param) ...))
   ]
  
  [(subst-ty program generic-decls params (mode borrowed leases ty))
   ((subst-mode program generic-decls mode)
    borrowed
    (subst-leases program generic-decls leases)
    (subst-ty program generic-decls params ty))]
  
  )

(define-metafunction dada
  subst-mode : program generic-decls params mode -> mode
  
  [(subst-mode program generic-decls params my) my]

  [(subst-mode program generic-decls params (shared leases))
   (shared (subst-leases program generic-decls params leases))]

  )

(define-metafunction dada
  subst-leases : program generic-decls params leases -> leases

  [(subst-leases program generic-decls params (lease ...))
   (lease_substituted ... ...)
   (where ((lease_substituted ...) ...) ((subst-lease program generic-decls params lease) ...))]

  )

(define-metafunction dada
  subst-lease : program generic-decls params lease -> leases
  
  [; Interesting case: when we find a parameter `p`, replace
   ; it with value from parameter list.
   (subst-lease program (generic-decl ...) (param ...) p)
   leases_p
   (where ((generic-decl_0 param_0) ... ((p _) leases_p) (generic-decl_1 param_1) ...) ((generic-decl param) ...))
   ]

  [; Otherwise, identity
   (subst-lease program generic-decls params (lease-kind place))
   ((lease-kind place))]

  )

(define-metafunction dada
  subst-param : program generic-decls params param -> param
  
  [(subst-param program generic-decls params ty)
   (subst-ty program generic-decls params ty)]

  [(subst-param program generic-decls params lease)
   (subst-lease program generic-decls params lease)]
  
  )

(define-metafunction dada
  ;; subst-ty xs places ty -> ty
  ;;
  ;; Replaces all references to the variables xs with the
  ;; corresponding place.
  subst-vars-in-ty : xs places ty -> ty

  [; Optimization: no parameters? identity
   (subst-vars-in-ty () () ty) ty]
  
  [; Interesting case: when we find a parameter `(mode p)`:
   ; * Find the corresponding type `ty_p` from the params list
   ; * Apply the mode `mode` to `ty_p`
   (subst-vars-in-ty xs places (mode p))
   (mode_subst p)
   (where mode_subst (subst-vars-in-mode xs places mode))
   ]

  ; Uninteresting cases: propagate the substitution downwards
  
  [(subst-vars-in-ty xs places int) int]
  
  [(subst-vars-in-ty xs places (dt (param ...)))
   (dt params_subst)
   (where params_subst ((subst-vars-in-param xs places param) ...))]
  
  [(subst-vars-in-ty xs places (mode c (param ...)))
   (mode_subst c params_subst)
   (where mode_subst (subst-vars-in-mode xs places mode))
   (where params_subst ((subst-vars-in-param xs places param) ...))
   ]
  
  [(subst-vars-in-ty program generic-decls params (mode borrowed leases ty))
   (mode_subst borrowed leases_subst ty_subst)
   (where mode_subst (subst-vars-in-mode xs places mode))
   (where leases_subst (subst-vars-in-leases xs places leases))
   (where ty_subst (subst-vars-in-ty xs places ty))
   ]
  
  )

(define-metafunction dada
  subst-vars-in-leases : xs places leases -> leases
  
  [(subst-vars-in-leases xs places (lease ...))
   ((subst-vars-in-lease xs places lease) ...)
   ]

  )
(define-metafunction dada
  subst-vars-in-lease : xs places lease -> lease
  
  [; Generic parameters are unaffected
   (subst-vars-in-lease xs places p)
   p
   ]

  [; 
   (subst-vars-in-lease xs places (lease-kind place))
   (lease-kind place_subst)
   (where place_subst (subst-vars-in-place xs places place))]

  )

(define-metafunction dada
  subst-vars-in-param : xs places param -> param
  
  [(subst-vars-in-param xs places ty)
   (subst-vars-in-ty xs places ty)]

  [(subst-vars-in-param xs places lease)
   (subst-vars-in-lease xs places lease)]
  
  )

(define-metafunction dada
  subst-vars-in-mode : xs places mode -> mode
  
  [(subst-vars-in-mode xs places my) my]

  [(subst-vars-in-mode xs places (shared leases))
   (shared (subst-vars-in-leases xs places leases))]
  
  )

(define-metafunction dada
  subst-vars-in-place : xs places place -> place
  
  [(subst-vars-in-place (x_0 ..._0 x x_1 ...) (place_0 ..._0 (pb_repl f_repl ...) place_1 ...) (x f ...))
   (pb_repl f_repl ... f ...)
   ]

  [(subst-vars-in-place xs places place) place]

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
    (ty_point (term (Point ())))
    (ty_shared_string (term (our String ())))
    (leases_x (term ((shared (x)))))
    (ty_some_shared_string (term (our Some (ty_shared_string))))
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

   (test-equal-terms (subst-vars-in-place (x-a x-b) ((x-a1) (x-b1 f-b1)) (x-b f1 f2))
                     (x-b1 f-b1 f1 f2))

   (test-equal-terms (subst-vars-in-place (x-a x-b) ((x-a1) (x-b1 f-b1)) (x-a f1 f2))
                     (x-a1 f1 f2))

   (test-equal-terms (subst-vars-in-ty
                      (vec element)
                      ((vec1) (element1))
                      ((shared ((shared (vec)))) String ()))
                     ((shared ((shared (vec1)))) String ()))

   )
  )
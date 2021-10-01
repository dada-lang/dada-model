#lang racket
(require redex "../grammar.rkt" "../util.rkt" "lang.rkt" "lease-implication.rkt")
(provide ty-assignable)

;; assignable program env ty_source ty_target
;;
;; Holds if a value of type `ty_source` can be assigned to a
;; place of type `ty_target`.
(define-judgment-form
  dada-type-system
  #:mode (ty-assignable I I I)
  #:contract (ty-assignable program ty ty)

  [--------------------------
   (ty-assignable program int int)]

  [(perms-assignable perms_source perms_target)
   --------------------------
   (ty-assignable _ (perms_source p) (perms_target p))]

  [(perms-assignable perms_source perms_target)
   (params-assignable program (class-variances program perms_source c) params_source params_target)
   --------------------------
   (ty-assignable program (perms_source c params_source) (perms_target c params_target))]
  )

(define-judgment-form
  dada-type-system
  #:mode (params-assignable I I I I)
  #:contract (params-assignable program variances params params)

  [(param-assignable program variance param_source param_target) ...
   --------------------------
   (params-assignable program (variance ...) (param_source ...) (param_target ...))]
  )

(define-judgment-form
  dada-type-system
  #:mode (param-assignable I I I I)
  #:contract (param-assignable program variance param param)

  [(ty-assignable program ty_1 ty_2)
   --------------------------
   (param-assignable program out ty_1 ty_2)]

  [--------------------------
   (param-assignable program _ param param)]
  )

(define-judgment-form
  dada-type-system
  #:mode (perms-assignable I I)
  #:contract (perms-assignable perms perms)

  [--------------------------
   (perms-assignable my my)]

  [--------------------------
   (perms-assignable my (shared _))]

  [--------------------------
   (perms-assignable my our)]

  [--------------------------
   (perms-assignable our (shared _))]

  [(leases-implied-by-leases leases_source leases_target)
   --------------------------
   (perms-assignable (shared leases_source) (shared leases_target))]

  [(leases-implied-by-leases leases_source leases_target)
   --------------------------
   (perms-assignable (lent leases_source) (lent leases_target))]
  )

(module+ test
  (redex-let*
   dada-type-system
   [(ty_my_string (term (my String ())))
    (ty_our_string (term (our String ())))
    (ty_my_vec_my_string (term (my Vec (ty_my_string))))
    (ty_our_vec_my_string (term (our Vec (ty_my_string))))
    (ty_our_vec_our_string (term (our Vec (ty_our_string))))
    (leases_lent_x (term ((lent (x)))))
    (leases_lent_xy (term ((lent (x)) (lent (y)))))
    (ty_lent_x_string (term ((lent leases_lent_x) String ())))
    (ty_lent_xy_string (term ((lent leases_lent_xy) String ())))
    (ty_lent_x_vec_my_string (term ((lent leases_lent_x) Vec (ty_my_string))))
    (ty_lent_x_vec_our_string (term ((lent leases_lent_x) Vec (ty_our_string))))
    ]

   (test-judgment-holds (ty-assignable program_test int int))
   (test-judgment-holds (ty-assignable program_test ty_my_string ty_my_string))
   (test-judgment-holds (ty-assignable program_test ty_my_string ty_our_string))

   ; my/our cannot be assigned to lent (as lent has a distinct representation)
   (test-judgment-false (ty-assignable program_test ty_my_string ty_lent_x_string))
   (test-judgment-false (ty-assignable program_test ty_our_string ty_lent_x_string))

   ; (lent x) <: (lent x|y) but not (naturally) vice versa
   (test-judgment-holds (ty-assignable program_test ty_lent_x_string ty_lent_xy_string))
   (test-judgment-false (ty-assignable program_test ty_lent_xy_string ty_lent_x_string))

   ; my Vec<my String> <: our Vec<my String>
   (test-judgment-holds (ty-assignable program_test ty_my_vec_my_string ty_our_vec_my_string))

   ; my Vec<my String> <: our Vec<our String>
   (test-judgment-holds (ty-assignable program_test ty_my_vec_my_string ty_our_vec_our_string))

   ; our Vec<my String> <: our Vec<our String>
   ;
   ; FIXME-- this doesn't hold because we don't apply the modes as we traverse;
   ; in essence `ty-assignable` expects the type to be "fully normalized" and `ty_our_vec_my_string`
   ; is not. Should we fix this?
   (test-judgment-false (ty-assignable program_test ty_our_vec_my_string ty_our_vec_our_string))

   ; lent Vec<my String> <: lent Vec<my String>
   (test-judgment-holds (ty-assignable program_test ty_lent_x_vec_my_string ty_lent_x_vec_my_string))

   ; lent Vec<my String> not <: lent Vec<our String>
   (test-judgment-false (ty-assignable program_test ty_lent_x_vec_my_string ty_lent_x_vec_our_string))
   )
  )


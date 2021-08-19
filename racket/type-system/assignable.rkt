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

  [(side-condition ,(pretty-print (term (mode-assignable mode_source mode_target))))
   (mode-assignable mode_source mode_target)
   --------------------------
   (ty-assignable _ (mode_source p) (mode_target p))]
  
  [(params-assignable program (datatype-variances program dt) params_source params_target)
   --------------------------
   (ty-assignable program (dt params_source) (dt params_target))]

  [(mode-assignable mode_source mode_target)
   (leases-implied-by-leases leases_source leases_target)
   (ty-assignable program ty_source ty_target)
   (ty-assignable program ty_target ty_source)
   --------------------------
   (ty-assignable program
                  (mode_source borrowed leases_source ty_source)
                  (mode_target borrowed leases_target ty_target))]

  [(params-assignable program (class-variances program c) params_source params_target)
   (mode-assignable mode_source mode_target)
   --------------------------
   (ty-assignable program (mode_source c params_source) (mode_target c params_target))]
  )

(define-judgment-form
  dada-type-system
  #:mode (params-assignable I I I I)
  #:contract (params-assignable program variances params params)

  [(side-condition (term (all (param-assignable program variance param_source param_target) ...)))
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
  #:mode (mode-assignable I I)
  #:contract (mode-assignable mode mode)

  [--------------------------
   (mode-assignable my my)]

  [--------------------------
   (mode-assignable my (shared _))]

  [(leases-implied-by-leases leases_source leases_target)
   --------------------------
   (mode-assignable (shared leases_source) (shared leases_target))]
  )

(module+ test
(redex-let*
 dada-type-system
 [(program program_test)
  (env_empty env_empty)
  (ty_my_string (term (my String ())))
  (ty_our_string (term (our String ())))
  ]

 (test-judgment-holds (ty-assignable program int int))
 (test-judgment-holds (ty-assignable program ty_my_string ty_my_string))
 (test-judgment-holds (ty-assignable program ty_my_string ty_our_string))
 )
)


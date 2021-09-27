#lang racket
(require redex
         data/order
         "../grammar.rkt"
         "../util.rkt"
         "lang.rkt")
(provide share-ty
         apply-mode
         )

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


(module+ test
  (redex-let*
   dada
   [(ty_my_string (term (my String ())))
    (ty_vec_string (term (my Vec (ty_my_string))))
    (ty_fn_string_string (term (my Fn (ty_my_string ty_my_string))))
    (ty_cell_string (term (my Cell (ty_my_string))))
    (ty_option_string (term (my Option (ty_my_string))))
    (ty_point (term (our Point ())))
    (leases_ours (term ()))
    (ty_shared_string (term (our String ())))
    (ty_option_shared_string (term (our Option (ty_shared_string))))
    (leases_x (term ((shared (x)))))
    ]

   ;; sharing a class affects mode *and* propagates to out parameters
   (test-equal-terms (share-ty program_test leases_ours ty_my_string) ty_shared_string)
   (test-equal-terms (share-ty program_test leases_ours ty_vec_string) ((shared ()) Vec (((shared ()) String ()))))

   ;; ...but not in or inout parameters
   (test-equal-terms (share-ty program_test leases_ours ty_fn_string_string) (our Fn (ty_my_string ty_shared_string)))
   (test-equal-terms (share-ty program_test leases_ours ty_cell_string) (our Cell (ty_my_string)))

   ;; sharing a datatype propagates to (out) parameters, but nothing else
   (test-equal-terms (share-ty program_test leases_ours ty_option_string) ty_option_shared_string)
   (test-equal-terms (share-ty program_test leases_ours ty_point) ty_point)

   ;; sharing something shared: no effect
   (test-equal-terms (share-ty program_test leases_x ty_shared_string) ty_shared_string)
   )
  )


#lang racket
(require redex
         "../grammar.rkt"
         "../util.rkt")
(provide apply-joint-mode-to-ty
         apply-mode
         )

(define-metafunction dada
  ;; apply-mode program mode ty
  ;;
  ;; Given the mode on a field owner, apply that mode to the type of
  ;; the field. Also used in other contexts.
  apply-mode : program mode ty -> ty

  [(apply-mode program my ty) ty]
  [(apply-mode program our ty) (apply-joint-mode-to-ty program our ty)]
  [(apply-mode program (lent leases) ty) (apply-unique-mode-to-ty program (lent leases) ty)]
  [(apply-mode program (shared leases) ty) (apply-joint-mode-to-ty program (shared leases) ty)]
  )

(define-metafunction dada
  ;; apply-joint-mode-to-ty program leases ty
  ;;
  ;; Transform a type by sharing it.
  apply-joint-mode-to-ty : program mode ty -> ty

  [;; "my" class becomes shared
   (apply-joint-mode-to-ty program mode_joint (my c (param ...)))
   (mode_joint c params_joint)
   (where (variance ...) (class-variances program my c))
   (where params_joint ((apply-joint-mode-to-param program mode_joint variance param) ...))
   ]

  [;; shared classes don't change
   (apply-joint-mode-to-ty program mode_joint ty)
   ty
   (where ((shared _) c _) ty)]

  [;; jointly owned classes don't change
   (apply-joint-mode-to-ty program mode_joint ty)
   ty
   (where (our c _) ty)]

  [;; data types don't change
   (apply-joint-mode-to-ty program mode_joint int)
   int]

  [;; generic types just alter their mode (further changes may result
   ;; after substitution)
   (apply-joint-mode-to-ty program mode_joint (mode_p p))
   (mode_out p)
   (where mode_out (apply-joint-mode-to-mode program mode_joint mode_p))]

  )

(define-metafunction dada
  ;; apply-joint-mode-to-mode program mode mode -> mode
  apply-joint-mode-to-mode : program mode mode -> mode

  [(apply-joint-mode-to-mode program mode my) mode]
  [(apply-joint-mode-to-mode program mode our) our]
  [;; sharing something that is already shared: just take the
   ;; original lease
   (apply-joint-mode-to-mode program mode (shared leases)) (shared leases)]
  )

(define-metafunction dada
  ;; apply-joint-mode-to-param program leases variance param -> mode
  ;;
  ;; Adjust the value `param` of a generic parameter which
  ;; has variance `variance` to account for being shared
  ;; for `leases`.
  apply-joint-mode-to-param : program mode variance param -> param

  [(apply-joint-mode-to-param program mode out ty) (apply-joint-mode-to-ty program mode ty)]
  [(apply-joint-mode-to-param program mode _ param) param]
  )

(define-metafunction dada
  apply-unique-mode-to-ty : program mode ty -> ty

  [;; classes: adjust the mode accordingly, but leave params untouched
   (apply-unique-mode-to-ty program mode_lent (mode_c c params))
   (mode_out c params)
   (where mode_out (apply-unique-mode-to-mode program mode_lent mode_c))
   ]

  [;; data types don't change
   (apply-unique-mode-to-ty program mode_lent int)
   int]

  [;; generic types just alter their mode (further changes may result
   ;; after substitution)
   (apply-unique-mode-to-ty program mode_lent (mode_p p))
   (mode_out p)
   (where mode_out (apply-unique-mode-to-mode program mode_lent mode_p))]
  )

(define-metafunction dada
  ;; apply-unique-mode-to-mode program mode_unique mode -> mode
  apply-unique-mode-to-mode : program mode_joint mode -> mode

  [(apply-unique-mode-to-mode program mode my) mode]
  [;; lending something that is already lent: retain the sublease
   ;; (e.g. if you have `lend x` and `x: ((lent L) T)`, then the resulting
   ;; type is `((lent (x)) T)`, a "sub-lease" of `x`, not `((lent L) T)`
   ;; (the original lease). This is different from joint modes
   (apply-unique-mode-to-mode program mode (lent _)) mode]
  [;; lending something that is jointly owned doesn't make sense; you just get a jointly
   ;; owned thing when you're done
   (apply-unique-mode-to-mode program mode our) our]
  [;; as with our, lending something that is shared doesn't change the fact that it's shared
   (apply-unique-mode-to-mode program mode (shared leases)) (shared leases)]
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
    (ty_shared_string (term (our String ())))
    (ty_option_shared_string (term (our Option (ty_shared_string))))
    (leases_x (term ((shared (x)))))
    (leases_lent_x (term ((lent (x)))))
    (leases_lent_y (term ((lent (y)))))
    ]

   ;; sharing a class affects mode *and* propagates to out parameters
   (test-equal-terms (apply-joint-mode-to-ty program_test our ty_my_string) ty_shared_string)
   (test-equal-terms (apply-joint-mode-to-ty program_test our ty_vec_string) (our Vec ((our String ()))))

   ;; ...but not in or inout parameters
   (test-equal-terms (apply-joint-mode-to-ty program_test our ty_fn_string_string) (our Fn (ty_my_string ty_shared_string)))
   (test-equal-terms (apply-joint-mode-to-ty program_test our ty_cell_string) (our Cell (ty_my_string)))

   ;; sharing a datatype propagates to (out) parameters, but nothing else
   (test-equal-terms (apply-joint-mode-to-ty program_test our ty_option_string) ty_option_shared_string)
   (test-equal-terms (apply-joint-mode-to-ty program_test our ty_point) ty_point)

   ;; sharing something shared: no effect
   (test-equal-terms (apply-joint-mode-to-ty program_test (shared leases_x) ty_shared_string) ty_shared_string)

   ;; joint ownership of a type parameter T
   (test-equal-terms (apply-mode program_test our (my T)) (our T))

   ;; lend a type parameter T
   (test-equal-terms (apply-mode program_test (lent leases_lent_x) (my T)) ((lent leases_lent_x) T))
   (test-equal-terms (apply-mode program_test (lent leases_lent_x) ((lent leases_lent_y) T)) ((lent leases_lent_x) T))
   (test-equal-terms (apply-mode program_test (lent leases_lent_x) (our T)) (our T))
   )
  )


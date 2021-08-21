#lang racket
(require redex
         data/order
         "../grammar.rkt"
         "../util.rkt")
(provide is-affine-ty
         is-copy-ty
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
    ]

   (test-judgment-holds (is-affine-ty ty_option_string))
   (test-judgment-false (is-affine-ty ty_shared_string))
   )
  )
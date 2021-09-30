#lang racket
(require redex
         data/order
         "../grammar.rkt"
         "../util.rkt")
(provide is-copy-ty
         )

(define-judgment-form dada
  #:mode (is-copy-ty I)
  #:contract (is-copy-ty ty)

  [--------------------------
   (is-copy-ty int)]

  [(is-copy-mode mode)
   --------------------------
   (is-copy-ty (mode c _))]

  [(is-copy-mode mode)
   --------------------------
   (is-copy-ty (mode p))]
  )

(define-judgment-form dada
  #:mode (is-copy-mode I)
  #:contract (is-copy-mode mode)

  [--------------------------
   (is-copy-mode our)]

  [--------------------------
   (is-copy-mode (shared _))]

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
    (ty_option_string (term (my Option (ty_my_string))))
    (ty_our_string (term (our String ())))
    (leases_x (term ((shared (x)))))
    (ty_shared_string (term ((shared leases_x) String ())))
    (leases_lent_x (term ((lent (x)))))
    (ty_lent_string (term ((lent leases_lent_x) String ())))
    ]

   (test-judgment-holds (is-copy-ty ty_our_string))
   (test-judgment-holds (is-copy-ty ty_shared_string))
   (test-judgment-holds (is-copy-ty int))
   (test-judgment-false (is-copy-ty ty_lent_string))
   )
  )
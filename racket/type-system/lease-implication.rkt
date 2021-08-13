#lang racket
(require redex data/order "../util.rkt" "../grammar.rkt")
(provide leases-implied-by-leases)

(define-judgment-form
  dada
  #:mode (leases-implied-by-leases I I)
  #:contract (leases-implied-by-leases leases leases)

  [(side-condition (all? (lease-implied-by-leases lease_source leases_target) ...))
   --------------------------
   (leases-implied-by-leases (lease_source ...) leases_target)]
  )

;; lease-implied-by-leases lease leases
;;
;; True if the rights granted by lease are covered by some
;; lease under leases.
(define-judgment-form
  dada
  #:mode (lease-implied-by-leases I I)
  #:contract (lease-implied-by-leases lease leases)

  [(lease-implied-by-lease lease_source lease_target)
   --------------------------
   (lease-implied-by-leases lease_source (lease_target0 ... lease_target lease_target1 ...))]
  )

(define-judgment-form
  dada
  #:mode (lease-implied-by-lease I I)
  #:contract (lease-implied-by-lease lease lease)

  [(lease-kind-implied-by-lease-kind lease-kind_source lease-kind_target)
   --------------------------
   (lease-implied-by-lease
    (lease-kind_source (x_target f_target ... f_source ...))
    (lease-kind_target (x_target f_target ...)))]
  )

(define-judgment-form
  dada
  #:mode (lease-kind-implied-by-lease-kind I I)
  #:contract (lease-kind-implied-by-lease-kind lease-kind lease-kind)

  [--------------------------
   (lease-kind-implied-by-lease-kind shared shared)]

  ;; If you already have a borrowed thing, a shared thing is a subset.
  [--------------------------
   (lease-kind-implied-by-lease-kind shared borrowed)]

  [--------------------------
   (lease-kind-implied-by-lease-kind borrowed borrowed)]
  )

(test-judgment-holds (lease-implied-by-leases (shared (x)) ((shared (x)))))
(test-judgment-false (lease-implied-by-leases (shared (x)) ((shared (y)))))
(test-judgment-holds (lease-implied-by-leases (shared (x y)) ((shared (x)))))
(test-judgment-false (lease-implied-by-leases (borrowed (x y)) ((shared (x)))))
(test-judgment-holds (lease-implied-by-leases (shared (x y)) ((borrowed (x)))))
(test-judgment-false (lease-implied-by-leases (shared (x)) ((shared (x y)))))

(test-judgment-false (leases-implied-by-leases ((shared (cell shv value)) atomic) ((shared (str)) (shared (cell shv value)))))

(test-judgment-holds (leases-implied-by-leases ((shared (x))) ((shared (x)))))
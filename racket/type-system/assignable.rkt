#lang racket
(require redex "../grammar.rkt" "../util.rkt" "lang.rkt")
(provide ty-assignable)

;; assignable program env ty_source ty_target
;;
;; Holds if a value of type `ty_source` can be assigned to a
;; place of type `ty_target`.
(define-judgment-form
  dada-type-system
  #:mode (ty-assignable I I I I)
  #:contract (ty-assignable program env ty ty)

  [--------------------------
   (ty-assignable program env int int)]

  [--------------------------
   (ty-assignable program env int int)]
  )

(define-judgment-form
  dada-type-system
  #:mode (mode-assignable I I I I)
  #:contract (mode-assignable program env mode mode)

  [--------------------------
   (mode-assignable program env my my)]

  [(leases-assignable program env leases_source leases_target)
   --------------------------
   (mode-assignable program env (shared leases_source) (shared leases_target))]
  )


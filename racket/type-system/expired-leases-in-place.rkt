#lang racket
(require racket/set redex
         "../grammar.rkt"
         "../util.rkt"
         "lang.rkt"
         "substitution.rkt")
(provide no-expired-leases-in-place
         no-expired-leases-traversing-place
         expired-leases-in-place?
         )

(define-metafunction dada-type-system
  expired-leases-in-place? : program env place -> boolean

  [(expired-leases-in-place? program env place)
   ,(not (judgment-holds (no-expired-leases-in-place program env place)))]

  )

(define-judgment-form dada-type-system
  ;; no-expired-leases-in-place program env place
  ;;
  ;; Evaluating `place` does not require traversing any expired leases.
  #:mode (no-expired-leases-in-place I I I)
  #:contract (no-expired-leases-in-place program env place)

  [------------------------
   (no-expired-leases-in-place program env (in-flight f ...))]

  [(where ty_place (place-ty program env place-at-rest))
   (no-expired-leases-traversing-place program env place-at-rest)
   (no-expired-leases-in-ty ty_place)
   ------------------------
   (no-expired-leases-in-place program env place-at-rest)]
  )

(define-judgment-form dada-type-system
  ;; no-expired-leases-traversing-place program env place
  ;;
  ;; Evaluating `place` does not require traversing any expired leases.
  #:mode (no-expired-leases-traversing-place I I I)
  #:contract (no-expired-leases-traversing-place program env place)

  [------------------------
   (no-expired-leases-traversing-place program env (x))]

  [(no-expired-leases-traversing-place program env (x f_0 ...))
   (where ty_0 (place-ty program env (x f_0 ...)))
   (no-expired-leases-traversing-ty ty_0)
   ------------------------
   (no-expired-leases-traversing-place program env (x f_0 ... f_1))]
  )

(define-judgment-form dada-type-system
  ;; no-expired-leases-traversing-ty ty
  ;;
  ;; Accessing a field of `ty` does not require
  ;; traversing an expired lease.
  #:mode (no-expired-leases-traversing-ty I)
  #:contract (no-expired-leases-traversing-ty ty)

  [(no-expired-leases-in-perms perms)
   ------------------------
   (no-expired-leases-traversing-ty (perms c _))]

  )

(define-judgment-form dada-type-system
  ;; no-expired-leases-in-ty program env ty
  #:mode (no-expired-leases-in-ty I)
  #:contract (no-expired-leases-in-ty ty)

  [------------------------
   (no-expired-leases-in-ty int)]

  [(no-expired-leases-in-param param) ...
   (no-expired-leases-in-perms perms)
   ------------------------
   (no-expired-leases-in-ty (perms c (param ...)))]

  )

(define-judgment-form dada-type-system
  ;; no-expired-leases-in-perms perms
  #:mode (no-expired-leases-in-perms I)
  #:contract (no-expired-leases-in-perms perms)

  [------------------------
   (no-expired-leases-in-perms my)]

  [------------------------
   (no-expired-leases-in-perms our)]

  [(no-expired-leases-in-leases leases)
   ------------------------
   (no-expired-leases-in-perms (shared leases))]

  [(no-expired-leases-in-leases leases)
   ------------------------
   (no-expired-leases-in-perms (lent leases))]
  )

(define-judgment-form dada-type-system
  ;; no-expired-leases-in-leases leases
  #:mode (no-expired-leases-in-leases I)
  #:contract (no-expired-leases-in-leases leases)

  [(lease-not-expired lease) ...
   ------------------------
   (no-expired-leases-in-leases (lease ...))]

  )

(define-judgment-form dada-type-system
  ;; no-expired-leases-in-param ty
  #:mode (no-expired-leases-in-param I)
  #:contract (no-expired-leases-in-param param)

  [(no-expired-leases-in-ty ty)
   ------------------------
   (no-expired-leases-in-param ty)]

  [(lease-not-expired lease) ...
   ------------------------
   (no-expired-leases-in-param (lease ...))]
  )

(define-judgment-form dada-type-system
  ;; not-expired lease
  #:mode (lease-not-expired I)
  #:contract (lease-not-expired lease)

  [------------------------
   (lease-not-expired p)]

  [------------------------
   (lease-not-expired atomic)]

  [------------------------
   (lease-not-expired (lease-kind place))]

  )

(module+ test
  (test-judgment-holds (no-expired-leases-in-ty int))
  (test-judgment-holds (no-expired-leases-in-ty (our String ())))
  (test-judgment-false (no-expired-leases-in-ty (our Vec (((shared (expired atomic)) String ())))))
  (test-judgment-holds (no-expired-leases-in-ty (our Vec (((shared (atomic)) String ())))))
  (test-judgment-false (no-expired-leases-in-ty ((lent (expired)) String ())))
  (test-judgment-false (no-expired-leases-in-ty (my Vec (((lent (expired)) String ())))))

  (redex-let*
   dada-type-system
   [(env (term (test-env (b ((lent (expired)) Character ())))))]
   (test-judgment-false (no-expired-leases-in-place program_test env (b ac)))
   )
  )

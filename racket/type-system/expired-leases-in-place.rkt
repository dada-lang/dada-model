#lang racket
(require racket/set redex "../grammar.rkt" "../util.rkt" "lang.rkt")
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

  [(where ty_place (place-ty program env place))
   (no-expired-leases-traversing-place program env place)
   (no-expired-leases-in-ty ty_place)
   ------------------------
   (no-expired-leases-in-place program env place)]
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

  [------------------------
   (no-expired-leases-traversing-ty (dt _))]

  [(no-expired-leases-in-mode mode)
   ------------------------
   (no-expired-leases-traversing-ty (mode c _))]

  [(no-expired-leases-in-mode mode)
   (no-expired-leases-in-leases leases)
   (no-expired-leases-traversing-ty ty)
   ------------------------
   (no-expired-leases-traversing-ty (mode borrowed leases ty))]
  )

(define-judgment-form dada-type-system
  ;; no-expired-leases-in-ty program env ty
  #:mode (no-expired-leases-in-ty I)
  #:contract (no-expired-leases-in-ty ty)

  [------------------------
   (no-expired-leases-in-ty int)]

  [(no-expired-leases-in-param param) ...
   ------------------------
   (no-expired-leases-in-ty (dt (param ...)))]

  [(no-expired-leases-in-param param) ...
   (no-expired-leases-in-mode mode)
   ------------------------
   (no-expired-leases-in-ty (mode c (param ...)))]

  [(no-expired-leases-in-leases leases)
   (no-expired-leases-in-mode mode)
   (no-expired-leases-in-ty ty)
   ------------------------
   (no-expired-leases-in-ty (mode borrowed leases ty))]
  
  )

(define-judgment-form dada-type-system
  ;; no-expired-leases-in-mode mode
  #:mode (no-expired-leases-in-mode I)
  #:contract (no-expired-leases-in-mode mode)

  [------------------------
   (no-expired-leases-in-mode my)]

  [(no-expired-leases-in-leases leases)
   ------------------------
   (no-expired-leases-in-mode (shared leases))]
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

(redex-let*
 dada-type-system
 [(program program_test)]
 (test-judgment-holds (no-expired-leases-in-ty int))
 (test-judgment-holds (no-expired-leases-in-ty (our String ())))
 (test-judgment-false (no-expired-leases-in-ty (our Vec (((shared (expired atomic)) String ())))))
 (test-judgment-holds (no-expired-leases-in-ty (our Vec (((shared (atomic)) String ())))))
 (test-judgment-false (no-expired-leases-in-ty (our borrowed (expired) (my String ()))))

 (redex-let*
  dada-type-system
  [(env (term (test-env (b (my borrowed (expired) (my Character ()))))))]
  (test-judgment-false (no-expired-leases-in-place program env (b ac)))
  )
 )
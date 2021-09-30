#lang racket
(require racket/set
         redex
         "../grammar.rkt"
         "../util.rkt"
         "lang.rkt"
         "expired-leases-in-place.rkt"
         "lease-scoping.rkt"
         )
(provide adjust-leases-in-env
         adjust-leases-in-ty)

(define-metafunction dada-type-system
  ;; adjust-leases-in-env program env action -> env
  ;;
  ;; Returns a new environment in which the leases that appear in
  ;; the local variables in `env` have been adjusted to account for `action`.
  ;; For example, if `action` is `(write (x))` and there was an active
  ;; lease of `(x)`, then the active lease would be transformed to `(expired)`.
  adjust-leases-in-env : program env action -> env

  [(adjust-leases-in-env program env action)
   (adjust-leases-in-env-fix program env env_out)
   (where ((x ty) ...) (var-tys-in-env env))
   (where env_out (env-with-var-tys env ((x (adjust-leases-in-ty program env ty action)) ...)))
   ]

  )

(define-metafunction dada-type-system
  ;; adjust-leases-in-env-fix program env_1 env_2 -> env
  ;;
  ;; Helper function that invokes `adjust-leases-in-env` again (with a noop action)
  ;; if a fixed point has not been reached.
  adjust-leases-in-env-fix : program env env -> env

  [(adjust-leases-in-env-fix program env env) env]

  [(adjust-leases-in-env-fix program env env_new) (adjust-leases-in-env program env_new noop)]

  )

(define-metafunction dada-type-system
  ;; adjust-leases-in-ty program env ty action -> ty
  ;;
  ;; Replace all leases in `ty` that are invalidated by `action` with `expired`
  adjust-leases-in-ty : program env ty action -> ty

  [(adjust-leases-in-ty program env int _) int]

  [(adjust-leases-in-ty program env (mode c (param ...)) action)
   (mode_expired c params_expired)
   (where mode_expired (adjust-leases-in-mode program env mode action))
   (where params_expired ((adjust-leases-in-param program env param action) ...))]

  [(adjust-leases-in-ty program env (mode p) action)
   (mode_expired p)
   (where mode_expired (adjust-leases-in-mode program env mode action))]

  )

(define-metafunction dada-type-system
  ;; adjust-leases-in-param program env param action -> param
  ;;
  ;; Replace all leases in `param` that are invalidated by `action` with `expired`
  adjust-leases-in-param : program env param action -> param

  [(adjust-leases-in-param program env ty action) (adjust-leases-in-ty program env ty action)]

  [(adjust-leases-in-param program env leases action) (adjust-leases-in-leases program env leases action)]
  )

(define-metafunction dada-type-system
  ;; adjust-leases-in-mode program env mode action -> mode
  ;;
  ;; Replace all leases in `mode` that are invalidated by `action` with `expired`
  adjust-leases-in-mode : program env mode action -> mode

  [(adjust-leases-in-mode program env my action) my]

  [(adjust-leases-in-mode program env our action) our]

  [(adjust-leases-in-mode program env (shared leases) action)
   (shared (adjust-leases-in-leases program env leases action))]

  [(adjust-leases-in-mode program env (lent leases) action)
   (lent (adjust-leases-in-leases program env leases action))]
  )

(define-metafunction dada-type-system
  ;; adjust-leases-in-leases program env leases action
  ;;
  ;; Adjusts the leases in `leases` based on `action`.
  adjust-leases-in-leases : program env leases action -> leases

  [; If any of the leases become expired, just return (expired) for the
   ; whole list. This isn't necessary but it's convenient.
   (adjust-leases-in-leases program env (lease_0 ... lease_1 lease_2 ...) action)
   (expired)
   (where (expired) (adjust-lease program env lease_1 action))]

  [(adjust-leases-in-leases program env (lease ...) action)
   (lease_adjusted ... ...)
   (where ((lease_adjusted ...) ...) ((adjust-lease program env lease action) ...))]

  )

(define-metafunction dada-type-system
  ;; adjust-lease program env lease action -> leases
  ;;
  ;; Transforms the lease to a new lease that reflects the
  ;; effect of `action`.

  adjust-lease : program env lease action -> leases

  [; If we have a lent lease on `a.b`, and the user reads `a.b.c`, then our lent lease is revoked.
   ; If we have a lent lease on `a.b.c`, and the user reads `a.b`, then our lent lease is revoked.
   ; If we have a lent lease on `a.b.c`, and the user reads `a.d`, then our lent lease is unaffected.
   (adjust-lease program env (lent place_1) (read place_2))
   (expired)
   (side-condition (term (places-overlapping? place_1 place_2)))]

  [; If we have a shared/lent lease on `a.b`, and the user writes to `a.b.c`, then our shared lease is revoked.
   ; If we have a shared/lent lease on `a.b.c`, and the user writes to `a.b`, then our shared lease is revoked.
   (adjust-lease program env (_ place_1) (write place_2))
   (expired)
   (side-condition (term (places-overlapping? place_1 place_2)))]

  [; If we have a shared lease on `a.b.c`, and the user moves `a.b`, then our lease is
   ; rewritten to be based on in-flight.
   (adjust-lease program env (shared (x f_0 ... f_1 ...)) (give (x f_0 ...)))
   ((shared (in-flight f_1 ...)))]

  [; If we have a lent lease on `a.b.c`, and the user moves `a.b`, then our lease is
   ; expired.
   ;
   ; FIXME: This could get more specific. If accessing c requires an indirection, or if
   ; a.b is boxed, this is not necessary!
   (adjust-lease program env (lent (x f_0 ... f_1 ...)) (give (x f_0 ...)))
   (expired)]

  [; If we have a shared/lent lease on `a.b`, and the user moves `a.b.c`, then our lease is expired.
   (adjust-lease program env (_ (x f_0 ...)) (give (x f_0 ... f_1 ...)))
   (expired)]

  [; Limit scoping of variables
   (adjust-lease program env lease (unscope-vars xs))
   (unscope-vars-in-lease program env lease xs)
   ]

  [; Storing the inflight-value
   (adjust-lease program env (lease-kind (in-flight f_1 ...)) (store-in-flight (x f_0 ...)))
   ((lease-kind (x f_0 ... f_1 ...)))
   ]

  [; Dropping the inflight-value
   (adjust-lease program env (lease-kind (in-flight f ...)) drop-in-flight)
   (expired)
   ]

  [; "Gather" remaps a lease on some temporary `x_old` to refer to a new place `pb_new f_new ...`.
   (adjust-lease program env (lease-kind (x_old f_old ...)) (gather ((x_0 _) ... (x_old (pb_new f_new ...)) (x_2 _) ...)))
   ((lease-kind (pb_new f_new ... f_old ...)))
   ]

  [; Any lease of a place that has become expired is itself expired.
   (adjust-lease program env (_ place_1) noop)
   (expired)
   (where #t (expired-leases-in-place? program env place_1))]

  [; For everything else, just return the lease unchanged.
   (adjust-lease program env lease _) (lease)]

  )

(module+ test

  (redex-let*
   dada-type-system
   [(env (term (test-env
                (x (my String ()))
                (y ((shared ((shared (x)))) String ())))))]

   (test-equal-terms
    (var-tys-in-env (adjust-leases-in-env program_test env (write (x))))
    ((y ((shared (expired)) String ())) (x (my String ())))
    ))

  (redex-let*
   dada-type-system
   [(env (term (test-env
                (x (my String ()))
                (y ((shared ((shared (x)))) String ()))
                (z ((shared ((shared (y)))) String ())))))]

   (test-equal-terms
    (var-tys-in-env (adjust-leases-in-env program_test env (write (x))))
    ((z ((shared (expired)) String ()))
     (y ((shared (expired)) String ()))
     (x (my String ())))
    )

   (test-equal-terms (adjust-leases-in-ty program_test env
                                          int (read (x)))
                     int)
   (test-equal-terms (adjust-leases-in-ty program_test env
                                          ((lent ((lent (x)))) String ()) (read (x)))
                     ((lent (expired)) String ()))
   (test-equal-terms (adjust-leases-in-ty program_test env
                                          ((shared ((lent (x)))) String ()) (read (x)))
                     ((shared (expired)) String ()))
   (test-equal-terms (adjust-leases-in-ty program_test env
                                          ((shared ((shared (x)))) String ()) (read (x)))
                     ((shared ((shared (x)))) String ()))
   (test-equal-terms (adjust-leases-in-ty program_test env
                                          ((shared ((shared (x)) atomic)) String ()) (write (x)))
                     ((shared (expired)) String ()))
   )

  (redex-let*
   dada-type-system
   [(env (term (test-env (x (my String ()))
                         (y ((shared ((shared (x)))) String ()))
                         (z ((shared ((shared (y)))) String ())))))]
   (test-equal-terms
    (var-tys-in-env (adjust-leases-in-env program_test env (write (x))))
    ((z ((shared (expired)) String ()))
     (y ((shared (expired)) String ()))
     (x (my String ())))))

  (redex-let*
   dada-type-system
   [(ty_pair_strings (term (my Pair ((my String ()) (my String ())))))
    (env (term (test-env (x ty_pair_strings)
                         (y ((lent ((lent (x)))) Pair ((my String ()) (my String ()))))
                         (z ((shared ((shared (y a)))) String ())))))]
   (test-equal-terms
    (var-tys-in-env (adjust-leases-in-env program_test env (write (x))))
    ((z ((shared (expired)) String ()))
     (y ((lent (expired)) Pair ((my String ()) (my String ()))))
     (x ty_pair_strings))))

  (redex-let*
   dada-type-system
   [(ty_pair_strings (term (my Pair ((my String ()) (my String ())))))
    (env (term (test-env (x ty_pair_strings)
                         (y ((lent ((lent (x)))) Pair ((my String ()) (my String ()))))
                         (z ((shared ((shared (y a)))) String ())))))]
   (test-equal-terms
    (var-tys-in-env (adjust-leases-in-env program_test env (unscope-vars (x))))
    ((z ((shared (expired)) String ()))
     (y ((lent (expired)) Pair ((my String ()) (my String ()))))
     (x ty_pair_strings))))

  (redex-let*
   dada-type-system
   [(ty_my_string (term (my String ())))
    (ty_pair_strings (term (my Pair (ty_my_string ty_my_string))))
    (mode_shared_x (term (shared ((shared (x))))))
    (env (term (test-env (x ty_pair_strings)
                         (y (mode_shared_x Pair (ty_my_string ty_my_string)))
                         (z ((shared ((shared (y a)))) String ())))))]
   (test-equal-terms
    (var-tys-in-env (adjust-leases-in-env program_test env (unscope-vars (y))))
    ((z (mode_shared_x String ()))
     (y (mode_shared_x Pair (ty_my_string ty_my_string)))
     (x ty_pair_strings))))

  (redex-let*
   dada-type-system
   [(ty_my_string (term (my String ())))
    (ty_pair_strings (term (my Pair (ty_my_string ty_my_string))))
    (mode_shared_x (term (shared ((shared (x))))))
    (env (term (test-env (x ty_pair_strings)
                         (y (mode_shared_x Pair (ty_my_string ty_my_string)))
                         (z ((shared ((shared (y a)))) String ())))))]
   (test-equal-terms
    (var-tys-in-env (adjust-leases-in-env program_test env (give (x))))
    ((z ((shared ((shared (y a)))) String ())) ; based on y, no change
     (y ((shared ((shared (in-flight)))) Pair (ty_my_string ty_my_string))) ; becomes in-flight
     (x ty_pair_strings) ; x
     )
    ))

  (redex-let*
   dada-type-system
   [(ty_my_string (term (my String ())))
    (ty_pair_strings (term (my Pair (ty_my_string ty_my_string))))
    (mode_shared_x (term (shared ((shared (x))))))
    (env (term (test-env (x ty_pair_strings)
                         (x1 ty_pair_strings)
                         (y (mode_shared_x Pair (ty_my_string ty_my_string)))
                         (z ((shared ((shared (y a)))) String ())))))]
   (test-equal-terms
    (var-tys-in-env
     (adjust-leases-in-env
      program_test
      (adjust-leases-in-env program_test env (give (x)))
      (store-in-flight (x1))))
    ((z ((shared ((shared (y a)))) String ())) ; based on y, no change
     (y ((shared ((shared (x1)))) Pair (ty_my_string ty_my_string))) ; becomes in-flight, then x1
     (x1 ty_pair_strings)
     (x ty_pair_strings) ; x
     )
    )
   )

  (redex-let*
   dada-type-system
   [(ty_my_string (term (my String ())))
    (ty_pair_strings (term (my Pair (ty_my_string ty_my_string))))
    (mode_shared_x (term (shared ((shared (x))))))
    (env (term (test-env (x ty_pair_strings)
                         (y (mode_shared_x Pair (ty_my_string ty_my_string)))
                         (z ((shared ((shared (y a)))) String ())))))]

   (test-equal-terms
    (var-tys-in-env
     (adjust-leases-in-env
      program_test
      (adjust-leases-in-env program_test env (give (x)))
      drop-in-flight))
    ((z ((shared (expired)) String ())) ; based on y, eventually expired
     (y ((shared (expired)) Pair (ty_my_string ty_my_string))) ; becomes in-flight, then expired
     (x ty_pair_strings) ; x
     )
    )
   )

  (redex-let*
   dada-type-system
   [(ty_my_string (term (my String ())))
    (ty_pair_strings (term (my Pair (ty_my_string ty_my_string))))
    (mode_shared_x (term (shared ((shared (x))))))
    (env (term (test-env (x ty_pair_strings)
                         (y (mode_shared_x Pair (ty_my_string ty_my_string)))
                         (z ((shared ((shared (y a)))) String ())))))]

   (test-equal-terms
    (var-tys-in-env
     (adjust-leases-in-env
      program_test
      env
      (gather ((x (in-flight)) (y (in-flight))))))
    ((z ((shared ((shared (in-flight a)))) String ()))
     (y ((shared ((shared (in-flight)))) Pair (ty_my_string ty_my_string)))
     (x ty_pair_strings) ; x
     )
    )
   )
  )
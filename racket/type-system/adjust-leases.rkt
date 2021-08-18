#lang racket
(require racket/set
         redex
         "../grammar.rkt"
         "../util.rkt"
         "lang.rkt"
         "expired-leases-in-place.rkt"
         "lease-scoping.rkt"
         )
(provide adjust-leases-in-env)

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

  [(adjust-leases-in-ty program env (dt (param ...)) action)
   (dt params_expired)
   (where params_expired ((adjust-leases-in-param program env param action) ...))]

  [(adjust-leases-in-ty program env (mode c (param ...)) action)
   (mode_expired c params_expired)
   (where mode_expired (adjust-leases-in-mode program env mode action))
   (where params_expired ((adjust-leases-in-param program env param action) ...))]

  [(adjust-leases-in-ty program env (mode borrowed leases ty) action)
   (mode_expired borrowed leases_expired ty_expired)
   (where mode_expired (adjust-leases-in-mode program env mode action))
   (where leases_expired (adjust-leases-in-leases program env leases action))
   (where ty_expired (adjust-leases-in-ty program env ty action))]

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

  [(adjust-leases-in-mode program env (shared leases) action) (shared (adjust-leases-in-leases program env leases action))]
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
  ;; adjust-lease program env lease action -> lease
  ;;
  ;; Transforms the lease to a new lease that reflects the
  ;; effect of `action`.
  
  adjust-lease : program env lease action -> leases

  [; If we have a borrowed lease on `a.b`, and the user reads `a.b.c`, then our borrowed lease is revoked.
   ; If we have a borrowed lease on `a.b.c`, and the user reads `a.b`, then our borrowed lease is revoked.
   ; If we have a borrowed lease on `a.b.c`, and the user reads `a.d`, then our borrowed lease is unaffected.
   (adjust-lease program env (borrowed place_1) (read place_2))
   (expired)
   (side-condition (term (places-overlapping? place_1 place_2)))]
  
  [; If we have a shared/borrowed lease on `a.b`, and the user writes to `a.b.c`, then our shared lease is revoked.
   ; If we have a shared/borrowed lease on `a.b.c`, and the user writes to `a.b`, then our shared lease is revoked.
   (adjust-lease program env (_ place_1) (write place_2))
   (expired)
   (side-condition (term (places-overlapping? place_1 place_2)))]

  [; For everything else, just return the lease unchanged.
   (adjust-lease program env lease (limit-scoping xs))
   (limit-scoping-in-lease program env lease xs)
   ]

  [; Any lease of a place that has become expired is itself expired.
   (adjust-lease program env (_ place_1) noop)
   (expired)
   (side-condition (term (expired-leases-in-place? program env place_1)))]
  
  [; For everything else, just return the lease unchanged.
   (adjust-lease program env lease _) (lease)]

  )

(redex-let*
 dada-type-system
 [(program program_test)
  (env (term (test-env
              (x (my String ()))
              (y ((shared ((shared (x)))) String ())))))]
            
 (test-equal-terms
  (var-tys-in-env (adjust-leases-in-env program env (write (x))))
  ((y ((shared (expired)) String ())) (x (my String ())))
  ))

(redex-let*
 dada-type-system
 [(program program_test)
  (env (term (test-env
              (x (my String ()))
              (y ((shared ((shared (x)))) String ()))
              (z ((shared ((shared (y)))) String ())))))]
            
 (test-equal-terms
  (var-tys-in-env (adjust-leases-in-env program env (write (x))))
  ((z ((shared (expired)) String ()))
   (y ((shared (expired)) String ()))
   (x (my String ())))
  )

 (test-equal-terms (adjust-leases-in-ty program env
                                        int (read (x)))
                   int)
 (test-equal-terms (adjust-leases-in-ty program env
                                        (my borrowed ((borrowed (x))) (my String ())) (read (x)))
                   (my borrowed (expired) (my String ())))
 (test-equal-terms (adjust-leases-in-ty program env
                                        ((shared ((borrowed (x)))) String ()) (read (x)))
                   ((shared (expired)) String ()))
 (test-equal-terms (adjust-leases-in-ty program env
                                        ((shared ((shared (x)))) String ()) (read (x)))
                   ((shared ((shared (x)))) String ()))
 (test-equal-terms (adjust-leases-in-ty program env
                                        ((shared ((shared (x)) atomic)) String ()) (write (x)))
                   ((shared (expired)) String ()))
 )

(redex-let*
 dada-type-system
 [(program program_test)
  (env (term (test-env (x (my String ()))
                       (y ((shared ((shared (x)))) String ()))
                       (z ((shared ((shared (y)))) String ())))))]
 (test-equal-terms
  (var-tys-in-env (adjust-leases-in-env program env (write (x))))
  ((z ((shared (expired)) String ()))
   (y ((shared (expired)) String ()))
   (x (my String ())))))

(redex-let*
 dada-type-system
 [(program program_test)
  (ty_pair_strings (term (my Pair ((my String ()) (my String ())))))
  (env (term (test-env (x ty_pair_strings)
                       (y (my borrowed ((borrowed (x))) ty_pair_strings))
                       (z ((shared ((shared (y a)))) String ())))))]
 (test-equal-terms
  (var-tys-in-env (adjust-leases-in-env program env (write (x))))
  ((z ((shared (expired)) String ()))
   (y (my borrowed (expired) ty_pair_strings))
   (x ty_pair_strings))))

(redex-let*
 dada-type-system
 [(program program_test)
  (ty_pair_strings (term (my Pair ((my String ()) (my String ())))))
  (env (term (test-env (x ty_pair_strings)
                       (y (my borrowed ((borrowed (x))) ty_pair_strings))
                       (z ((shared ((shared (y a)))) String ())))))]
 (test-equal-terms
  (var-tys-in-env (adjust-leases-in-env program env (limit-scoping (y z))))
  ((z ((shared (expired)) String ()))
   (y (my borrowed (expired) ty_pair_strings))
   (x ty_pair_strings))))

(redex-let*
 dada-type-system
 [(program program_test)
  (ty_my_string (term (my String ())))
  (ty_pair_strings (term (my Pair (ty_my_string ty_my_string))))
  (mode_shared_x (term (shared ((shared (x))))))
  (env (term (test-env (x ty_pair_strings)
                       (y (mode_shared_x Pair (ty_my_string ty_my_string)))
                       (z ((shared ((shared (y a)))) String ())))))]
 (test-equal-terms
  (var-tys-in-env (adjust-leases-in-env program env (limit-scoping (x z))))
  ((z (mode_shared_x String ()))
   (y (mode_shared_x Pair (ty_my_string ty_my_string)))
   (x ty_pair_strings))))
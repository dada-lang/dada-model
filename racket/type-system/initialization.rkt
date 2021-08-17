#lang racket
(require racket/set redex "../grammar.rkt" "../util.rkt" "lang.rkt")
(provide definitely-initialized?
         maybe-initialized?
         definitely-not-initialized?
         place-initializable
         env-with-initialized-place
         env-with-deinitialized-place
         no-expired-leases-in-place
         no-expired-leases-traversing-place
         expire-leases-in-env
         )

(define-metafunction dada-type-system
  ;; definitely-initialized? env place -> boolean
  ;;
  ;; True if place is definitely initialized
  definitely-initialized? : env place -> boolean
  [(definitely-initialized? env place)
   (place-or-prefix-in? place (definitely-initialized-places env))])

(define-metafunction dada-type-system
  ;; maybe-initialized env place -> boolean
  ;;
  ;; True if place may be initialized
  maybe-initialized? : env place -> boolean
  [(maybe-initialized? env place)
   (place-or-prefix-in? place (maybe-initialized-places env))])

(define-metafunction dada-type-system
  ;; definitely-not-initialized env place -> boolean
  ;;
  ;; True if place is definitely initialized
  definitely-not-initialized? : env place -> boolean
  [(definitely-not-initialized? env place)
   (not? (maybe-initialized? env place))])

(define-judgment-form dada-type-system
  ;; place-initializable env place
  ;;
  ;; True if it is legal to initialize `place`. True for local variables
  ;; or, given a place `a.b.c`, if the prefix `a.b` is initialized.
  #:mode (place-initializable I I)
  #:contract (place-initializable env place)

  [;; Local variables can always be initialized
   -----------------------
   (place-initializable env (x))]

  [;; Assigning to `a.b.c` is possible if some prefix `a` is initialized
   ;; (note that `a.b.*` may equal `a.b` or `a.b.c`).
   (where (place_0 ... (x f_0 ...) place_1 ...) (definitely-initialized-places env))
   -----------------------
   (place-initializable env (x f_0 ... f_1 ...))]
  
  [;; Assigning to `a.b.c` is possible if some `a.b.*` is initialized
   (where (place_0 ... (x f_0 ... f_2 ...) place_1 ...) (definitely-initialized-places env))
   -----------------------
   (place-initializable env (x f_0 ... f_1))]
  )
  
(redex-let*
 dada-type-system
 [(env (term ((maybe-init ((x) (y f) (y g)))
              (def-init ((x) (y f)))
              (vars ())
              ())))]
 (test-equal (term (definitely-initialized? env (x))) #t)
 (test-equal (term (definitely-initialized? env (z))) #f)
 (test-equal (term (definitely-initialized? env (y f))) #t)
 (test-equal (term (definitely-initialized? env (y f f1))) #t)
 (test-equal (term (definitely-initialized? env (y g))) #f)
 (test-equal (term (maybe-initialized? env (y f g))) #t)
 (test-equal (term (maybe-initialized? env (y g h))) #t)
 (test-equal (term (maybe-initialized? env (y h))) #f)
 (test-equal (term (definitely-not-initialized? env (y h))) #t)
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

(define-metafunction dada-type-system
  ;; expire-leases-in-env program env action -> env
  ;;
  ;; Returns a new environment in which the leases that appear in
  ;; the local variables in `env` have been adjusted to account for `action`.
  ;; For example, if `action` is `(write (x))` and there was an active
  ;; lease of `(x)`, then the active lease would be transformed to `(expired)`.
  expire-leases-in-env : program env action -> env

  [(expire-leases-in-env program env action)
   (expire-leases-in-env-fix program env env_out)
   (where ((x ty) ...) (var-tys-in-env env))
   (where env_out (env-with-var-tys env ((x (expire-leases-in-ty program env ty action)) ...)))
   ]

  )

(define-metafunction dada-type-system
  ;; expire-leases-in-env-fix program env_1 env_2 -> env
  ;;
  ;; Helper function that invokes `expire-leases-in-env` again (with a noop action)
  ;; if a fixed point has not been reached.
  expire-leases-in-env-fix : program env env -> env

  [(expire-leases-in-env-fix program env env) env]

  [(expire-leases-in-env-fix program env env_new) (expire-leases-in-env program env_new noop)]

  )

(define-metafunction dada-type-system
  ;; expire-leases-in-ty program env ty action -> ty
  ;;
  ;; Replace all leases in `ty` that are invalidated by `action` with `expired`
  expire-leases-in-ty : program env ty action -> ty

  [(expire-leases-in-ty program env int _) int]

  [(expire-leases-in-ty program env (dt (param ...)) action)
   (dt params_expired)
   (where params_expired ((expire-leases-in-param program env param action) ...))]

  [(expire-leases-in-ty program env (mode c (param ...)) action)
   (mode_expired c params_expired)
   (where mode_expired (expire-leases-in-mode program env mode action))
   (where params_expired ((expire-leases-in-param program env param action) ...))]

  [(expire-leases-in-ty program env (mode borrowed leases ty) action)
   (mode_expired borrowed leases_expired ty_expired)
   (where mode_expired (expire-leases-in-mode program env mode action))
   (where leases_expired (expire-leases-in-leases program env leases action))
   (where ty_expired (expire-leases-in-ty program env ty action))]

  [(expire-leases-in-ty program env (mode p) action)
   (mode_expired p)
   (where mode_expired (expire-leases-in-mode program env mode action))]

  )

(define-metafunction dada-type-system
  ;; expire-leases-in-param program env param action -> param
  ;;
  ;; Replace all leases in `param` that are invalidated by `action` with `expired`
  expire-leases-in-param : program env param action -> param

  [(expire-leases-in-param program env ty action) (expire-leases-in-ty program env ty action)]

  [(expire-leases-in-param program env leases action) (expire-leases-in-leases program env leases action)]
  )

(define-metafunction dada-type-system
  ;; expire-leases-in-mode program env mode action -> mode
  ;;
  ;; Replace all leases in `mode` that are invalidated by `action` with `expired`
  expire-leases-in-mode : program env mode action -> mode

  [(expire-leases-in-mode program env my action) my]

  [(expire-leases-in-mode program env (shared leases) action) (shared (expire-leases-in-leases program env leases action))]
  )

(define-metafunction dada-type-system
  ;; expired-leases-in-leases program env leases action
  ;;
  ;; If any of the leases in `leases` are invalidated by `action`, returns `(expired)`.
  ;;
  ;; Else returns `leases`.
  expire-leases-in-leases : program env leases action -> leases

  [(expire-leases-in-leases program env (lease_0 ... lease_1 lease_2 ...) action)
   (expired)
   (side-condition (term (lease-invalidated-by-action? program env lease_1 action)))]

  [(expire-leases-in-leases program env leases action)
   leases]
  
  )

(define-metafunction dada-type-system
  ;; lease-invalidated-by-action? lease action
  ;;
  ;; True if taking the action `action` invalidates the given `lease`.
  
  lease-invalidated-by-action? : program env lease action -> boolean

  ;; Examples:
  ;;
  ;; If we have a borrowed lease on `a.b`, and the user reads `a.b.c`, then our borrowed lease is revoked.
  ;; If we have a borrowed lease on `a.b.c`, and the user reads `a.b`, then our borrowed lease is revoked.
  ;; If we have a borrowed lease on `a.b.c`, and the user reads `a.d`, then our borrowed lease is unaffected.
  [(lease-invalidated-by-action? program env (borrowed place_1) (read place_2)) (places-overlapping? place_1 place_2)]
  
  ;; If we have a shared/borrowed lease on `a.b`, and the user writes to `a.b.c`, then our shared lease is revoked.
  ;; If we have a shared/borrowed lease on `a.b.c`, and the user writes to `a.b`, then our shared lease is revoked.
  [(lease-invalidated-by-action? program env (_ place_1) (write place_2)) (places-overlapping? place_1 place_2)]

  ;; If we have a shared lease on `a.b`, and the user reads some memory (no matter what), our lease is unaffected.
  [(lease-invalidated-by-action? program env (shared place_1) (read place_2)) #f]

  [(lease-invalidated-by-action? program env (_ place_1) noop) (expired-leases-in-place? program env place_1)]

  [(lease-invalidated-by-action? program env expired _) #f]

  [(lease-invalidated-by-action? program env atomic _) #f]
  
  )

(redex-let*
 dada-type-system
 [(program program_test)
  (env (term (test-env
              (x (my String ()))
              (y ((shared ((shared (x)))) String ())))))]
            
 (test-equal-terms
  (var-tys-in-env (expire-leases-in-env program env (write (x))))
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
  (var-tys-in-env (expire-leases-in-env program env (write (x))))
  ((z ((shared (expired)) String ()))
   (y ((shared (expired)) String ()))
   (x (my String ())))
  )

 (test-equal-terms (expire-leases-in-ty program env
                                        int (read (x)))
                   int)
 (test-equal-terms (expire-leases-in-ty program env
                                        (my borrowed ((borrowed (x))) (my String ())) (read (x)))
                   (my borrowed (expired) (my String ())))
 (test-equal-terms (expire-leases-in-ty program env
                                        ((shared ((borrowed (x)))) String ()) (read (x)))
                   ((shared (expired)) String ()))
 (test-equal-terms (expire-leases-in-ty program env
                                        ((shared ((shared (x)))) String ()) (read (x)))
                   ((shared ((shared (x)))) String ()))
 (test-equal-terms (expire-leases-in-ty program env
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
  (var-tys-in-env (expire-leases-in-env program env (write (x))))
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
  (var-tys-in-env (expire-leases-in-env program env (write (x))))
  ((z ((shared (expired)) String ()))
   (y (my borrowed (expired) ty_pair_strings))
   (x ty_pair_strings))))

(define-metafunction dada-type-system
  ;; (place-extensions program env place) -> places
  ;;
  ;; Given a place like `a.b`, yields all legal extensions
  ;; (e.g., `a.b.c`, a.b.d`) that add a single field.
  place-extensions : program env place -> places
  [(place-extensions program env place)
   ((x f ... f_place) ...)
   (where ty_place (place-ty program env place))
   (where (f_place ...) (field-names program ty_place))
   (where (x f ...) place)
   ]

  )

(define-metafunction dada-type-system
  ;; (place-prefix-in place places) -> place
  ;;
  ;; Yields the prefix of `place` found in `places`.
  place-prefix-in : place places -> place
  [(place-prefix-in place places)
   (x_prefix f_prefix ...)
   (where (place_0 ... (x_prefix f_prefix ...) place_1 ...) places)
   (where (x_prefix f_prefix ... f_other ...) place)
   ]
  )

(define-metafunction dada-type-system
  ;; (any-places-overlapping? places)
  ;;
  ;; Checks if any two places in `places` are overlapping.
  any-places-overlapping? : places -> boolean
  [(any-places-overlapping? places)
   #t
   (where (place_0 ... place_a place_2 ... place_b place_3 ...) places)
   (side-condition (term (places-overlapping? place_a place_b)))
   ]
  [(any-places-overlapping? places) #f]
  )

(define-metafunction dada-type-system
  ;; partition-places place places -> (places_overlapping places_other)
  ;;
  ;; Splits a list of places `places` into those places that overlap with `place`
  ;; and those that do not.
  partition-places : place places -> (places_overlapping places_other)

  [(partition-places place places)
   ,(partition-list (λ (p) (term (places-overlapping? ,p place))) (term places))
   ]
  )

(define-metafunction dada-type-system
  is-minimal-with-respect-to-prefix? : program env place_prefix places_in -> boolean
  #:pre (all? (not? (any-places-overlapping? places_in))
              (not? (place-or-prefix-in? place_prefix places_in)))

  [(is-minimal-with-respect-to-prefix? program env place_prefix places_in)
   (missing-fields? places_ext places_ext-all)
   (where (places_ext _) (partition-places place_prefix places_in))
   (where places_ext-all (place-extensions program env place_prefix))
   ]
  )

(define-metafunction dada
  ;; missing-fields? places_present places_all
  ;;
  ;; True if the set of places in `places_present` represents all
  ;; the fields cited in `places_all`. At all times the former
  ;; must be a subset of the latter. This is used when extending
  ;; and expanding places, so e.g. `places_all` might be something like
  ;; `p.x` and `p.y` (for a point `p`), and `places_present` some subset
  ;; of those.
  missing-fields? : places_present places_all -> boolean
  #:pre ,(subset? (term places_present) (term places_all))
  [(missing-fields? places_1 places_2)
   ,(proper-subset? (term places_1) (term places_2))
   ]
  )

(define-metafunction dada-type-system
  ;; is-minimal? program env places
  ;;
  ;; A set of places `places` is *minimal* if there is no place `p`
  ;; where `places` contains (`p.f1` ... `p.fN`) for each field `f1...fN`
  ;; that can extend the place `p`. In that case, `places` should just
  ;; contain `p`.
  is-minimal? : program env places_in -> boolean
  #:pre (not? (any-places-overlapping? places_in))

  [(is-minimal? program env places) (not? (is-not-minimal? program env places))]
  )

(define-metafunction dada-type-system
  is-not-minimal? : program env places_in -> boolean
  #:pre (not? (any-places-overlapping? places_in))

  [(is-not-minimal? program env (place_0 ... (x f ... f_last) place_1 ...))
   (not? (is-minimal-with-respect-to-prefix? program env (x f ...) (place_0 ... (x f ... f_last) place_1 ...)))
   ]

  [(is-not-minimal? program env places) #f]
  )

(define-metafunction dada-type-system
  ;; minimize-places program env place_prefix places_in -> places_out
  ;;
  ;; Given a list of places `places_in` that contains various
  ;; extensions of `place_prefix`, returns an equivalent *minimal* set
  ;; of places.  For example if:
  ;;
  ;; * a variable `p: Point` where `data Point(x: int, y: int)`
  ;; * `place_prefix` is `(p)`
  ;; * and `places_in` is `((p x) (p y))`
  ;;
  ;; then we would return `((p))`, because all fields of `p` are
  ;; contained in the set, so we can just say that `p` itself
  ;; is initialized.
  minimize-places : program_in env_in place_prefix places_in -> places_out
  #:pre (all? (not? (any-places-overlapping? places_in))
              (not? (place-or-prefix-in? place_prefix places_in)))
  #:post (all? (not? (any-places-overlapping? places_out))
               (is-minimal? program_in env_in places_out))

  [(minimize-places program env place_prefix places_in)
   (minimize-places-fix program env place_prefix (place_other ... place_prefix))
   (side-condition (term (not? (is-minimal-with-respect-to-prefix? program env place_prefix places_in))))
   (where (_ (place_other ...)) (partition-places place_prefix places_in))
   ]

  [(minimize-places program env place_prefix places_in)
   places_in
   ]
  )

(define-metafunction dada-type-system
  ;; minimize-places-fix program env place places
  ;;
  ;; Helper function: place is a prefix that was just added to places.
  ;; Check whether we need to recursively minimize. This occurs
  ;; when you e.g. adding `a.b.c` let's us find that `a.b` is fully initialized,
  ;; which in turn may mean that `a` is fully initialized.
  minimize-places-fix : program_in env_in place_in places_in -> places_out
  #:pre (all? (not? (any-places-overlapping? places_in))
              (place-in? place_in places_in))
  #:post (all? (not? (any-places-overlapping? places_out))
               (is-minimal? program_in env_in places_out))

  [(minimize-places-fix program env (x f ... f_last) places_in)
   (minimize-places program env (x f ...) places_in)
   ]

  [(minimize-places-fix program env (x) places_in)
   places_in]
  )

(define-judgment-form dada-type-system
  ;; (initialize-place program env place places_in places_out)
  ;;
  ;; Given a list of places (`places_in`) that is either maybe
  ;; or definitely initialized, adds `place` to that list, adjusting
  ;; the list as needed to ensure the `any-places-overlapping?` property
  ;; is maintained.
  #:mode (places-with-initialized-place I I I I O)
  #:contract (places-with-initialized-place program env place places_in places_out)
  #:inv (not? (any-places-overlapping? places_out))

  ;; If some prefix of this place is already initialized,
  ;; then nothing changes.
  [(side-condition (place-or-prefix-in? place places_in))
   -----------------------
   (places-with-initialized-place program env place places_in places_in)]

  ;; Difficult case: initialize a place with fields, like `(some-point x)`,
  ;; that is not already initialized. This is tricky because
  ;; it may make the set "non-minimal" -- i.e., if `(some-point y)` is
  ;; already initialized, then the best set is `((some-point))`, not
  ;; `((some-point x) (some-point y))`.
  [(side-condition (not? (place-or-prefix-in? place places_in)))
   ; Rule only applies when we have a prefix:
   (where (x f ... f_last) place)
   (where place_prefix (x f ...))
   ; given that no prefix of place appears in `place_in`,
   ; all overlapping places must be extensions of `place` that will
   ; get overwritten.
   (where (_ (place_other ...)) (partition-places place places_in))
   ; construct that minimal set of outout places:
   (where places_mid (place place_other ...))
   (where places_out (minimize-places program env place_prefix places_mid))
   -----------------------
   (places-with-initialized-place program env place places_in places_out)]

  ; Easier case: initialize a variable that is not already
  ; initialized (or which is partly initialized).
  [(side-condition (not? (place-or-prefix-in? (x) places_in)))
   (where (_ (place_other ...)) (partition-places (x) places_in))
   -----------------------
   (places-with-initialized-place program env (x) places_in ((x) place_other ...))]

  )

(define-judgment-form dada-type-system
  #:mode (env-with-initialized-place I I I O)
  #:contract (env-with-initialized-place program env place env_out)

  [(where env_tl (expire-leases-in-env program env (write place)))
   (places-with-initialized-place program env_tl place (definitely-initialized-places env_tl) places_def)
   (places-with-initialized-place program env_tl place (maybe-initialized-places env_tl) places_maybe)
   (where env_out (env-with-initialized-places env_tl places_def places_maybe))
   -----------------------
   (env-with-initialized-place program env place env_out)]
  )

(define-judgment-form dada-type-system
  #:mode (places-with-deinitialized-place I I I I O)
  #:contract (places-with-deinitialized-place program env place_in places_in places_out)
  #:inv (all? (place-or-prefix-in? place_in places_in)
              (not? (any-places-overlapping? places_out)))

  ;; If this place is directly in the list, that's the easy case,
  ;; just remove it.
  [-----------------------
   (places-with-deinitialized-place program env place (place_0 ... place place_1 ...) (place_0 ... place_1 ...))]

  [(where (place_ext ...) (place-extensions program env (x f ...)))
   (places-with-deinitialized-place program env (x f ... f_extra ...) (place_0 ... place_ext ... place_1 ...) places_out)
   -----------------------
   (places-with-deinitialized-place program env (x f ... f_extra ...) (place_0 ... (x f ...) place_1 ...) places_out)]
  )

(define-judgment-form dada-type-system
  #:mode (env-with-deinitialized-place I I I O)
  #:contract (env-with-deinitialized-place program env place env_out)

  [(where env_tl (expire-leases-in-env program env (write place)))
   (places-with-deinitialized-place program env_tl place (definitely-initialized-places env_tl) places_def)
   (places-with-deinitialized-place program env_tl place (maybe-initialized-places env_tl) places_maybe)
   (where env_out (env-with-initialized-places env_tl places_def places_maybe))
   -----------------------
   (env-with-deinitialized-place program env place env_out)]
  )

(redex-let*
 dada-type-system
 [(program program_test)
  (ty_my_string (term (my String ())))
  (ty_my_character (term (my Character ())))
  (ty_my_pair (term (my Pair (ty_my_string ty_my_character))))
  (env (term ((maybe-init ((a-point) (a-character)))
              (def-init ((a-point) (a-character)))
              (vars ((a-point (Point ()))
                     (a-character (my Character ()))
                     (some-character (Some ((my Character ()))))
                     (a-pair ty_my_pair)))
              ())))
  (place_character (term (a-character)))

  ; for some reason, if I put `(a-pair b name)` in place below, dr racket gives me an odd error
  (places_remaining (term ((a-pair a) (a-pair b name) (a-pair b ac))))
  ]
 
 (test-equal-terms (place-extensions program env place_character)
                   ((a-character hp) (a-character name) (a-character ac)))
 (test-equal-terms (place-prefix-in (a-character ac) ((a-point) (a-character))) (a-character))
 (test-equal-terms (place-prefix-in (a-character ac) ((a-character) (a-point))) (a-character))
 
 (test-equal-terms (any-places-overlapping? ((a-character) (a-character ac))) #t)
 (test-equal-terms (any-places-overlapping? ((a-character ac) (a-character ac))) #t)
 (test-equal-terms (any-places-overlapping? ((a-character ac) (a-character))) #t)

 (test-equal-terms (any-places-overlapping? ((a-character ac) (a-point) (a-character))) #t)

 (test-equal-terms (any-places-overlapping? ((a-character ac) (a-point) (a-character hp))) #f)

 (test-equal-terms (partition-places (a b c) ((a) (a b d) (a b c) (a b c d) (a b e))) (((a) (a b c) (a b c d))
                                                                                       ((a b d) (a b e))))

 (test-judgment-holds (places-with-initialized-place program env
                                                     (a-character ac)
                                                     ((a-character hp))
                                                     ((a-character ac) (a-character hp))))

 (test-judgment-holds (places-with-initialized-place program env
                                                     (a-character ac)
                                                     ((a-character hp) (a-character name))
                                                     ((a-character))))

 (test-judgment-holds (places-with-initialized-place program env
                                                     (a-pair b ac)
                                                     ((a-pair b hp) (a-pair b name))
                                                     ((a-pair b))))

 (test-judgment-holds (places-with-initialized-place program env
                                                     (a-pair b ac)
                                                     ((a-pair a) (a-pair b hp) (a-pair b name))
                                                     ((a-pair))))

 (test-judgment-holds (places-with-initialized-place program env
                                                     (a-pair b ac)
                                                     ((a-pair))
                                                     ((a-pair))))

 (test-judgment-holds (places-with-initialized-place program env
                                                     (a-pair)
                                                     ()
                                                     ((a-pair))))

 (test-judgment-holds (places-with-initialized-place program env
                                                     (a-pair b)
                                                     ()
                                                     ((a-pair b))))

 (test-judgment-holds (places-with-deinitialized-place program env
                                                       (a-pair b hp)
                                                       ((a-pair b hp) (a-pair a))
                                                       ((a-pair a))))

 (test-judgment-holds (places-with-deinitialized-place program env
                                                       (a-pair b hp)
                                                       ((a-pair))
                                                       places_remaining))
 )
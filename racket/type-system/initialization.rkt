#lang racket
(require racket/set redex "../grammar.rkt" "../util.rkt" "lang.rkt")
(provide definitely-initialized?
         maybe-initialized?
         definitely-not-initialized?
         env-with-initialized-place
         env-with-deinitialized-place
         terminate-lease
         )

;; definitely-initialized env place -> boolean
;;
;; True if place is definitely initialized
(define-metafunction dada-type-system
  definitely-initialized? : env place -> boolean
  [(definitely-initialized? env place)
   (place-or-prefix-in? place (definitely-initialized-places env))])

;; maybe-initialized env place -> boolean
;;
;; True if place may be initialized
(define-metafunction dada-type-system
  maybe-initialized? : env place -> boolean
  [(maybe-initialized? env place)
   (place-or-prefix-in? place (maybe-initialized-places env))])

;; definitely-not-initialized env place -> boolean
;;
;; True if place is definitely initialized
(define-metafunction dada-type-system
  definitely-not-initialized? : env place -> boolean
  [(definitely-not-initialized? env place)
   (not? (maybe-initialized? env place))])

(redex-let*
 dada-type-system
 [(env (term ((maybe-init ((x) (y f) (y g)))
              (def-init ((x) (y f)))
              (vars ()))))]
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


;; terminate-leave program env lease-kind place -> env
;;
;; Removes any places from the list of "definitely initialized"
;; places whose types may reference `(lease-kind place)`.
;;
;; Note that `place` may not be initialized (in which case
;; there would be no types to remove).
;;
;; This is used after place is accessed, and the lease-kind
;; is the kind of lease that is invalidated by that access.
;; So, for example, if we have a read of `x`, then we would
;; remove all places that have a type like that references
;; `borrowed x`.
;;
;; Note that these places remain in the 'maybe initialized'
;; list, which permits them to be dropped. This is ok because
;; dropping something of "shared/borrowed" mode has no effect.
;;
;; FIXME: For now, we just remove the entire place from
;; being considered initialized. At some point we might replace
;; it with more refined paths that are unaffected.
(define-metafunction dada-type-system
  terminate-lease : program env_in action-kind place_in -> env_out

  ; If `place_in` is not initialized on entry, then it can't
  ; have appeared in any active leases.
  #:post (any? (definitely-initialized? env_in place_in)
               (env-equal? env_in env_out))

  [(terminate-lease program env action-kind place)
   (env-with-definitely-initialized-places env places_remaining)
   (where places_def_init (definitely-initialized-places env))
   (where action (action-kind place))
   (where places_remaining (terminate-lease-places program env action places_def_init))
   ]
  )

(define-metafunction dada-type-system
  terminate-lease-places : program env action places -> places

  [(terminate-lease-places program env action places_def_init)
   (terminate-lease-places-fix program env places_remaining0 places_invalidated)
   (where (places_invalidated places_remaining0) ,(partition-list (λ (place) (term (place-invalidated-by-action? program env ,place action))) (term places_def_init)))
   ])

;; terminate-lease-fix program env places_def_init places_invalidated -> env
;;
;; Invoked with a lits of invalidated places.
(define-metafunction dada-type-system
  terminate-lease-places-fix : program env places places -> places

  [(terminate-lease-places-fix program env places_remaining ()) places_remaining]
  [(terminate-lease-places-fix program env places_remaining0 (place_0 place_1 ...))
   (terminate-lease-places-fix program env places_remaining1 (place_1 ...))
   (where action (write place_0))
   (where places_remaining1 (terminate-lease-places program env action places_remaining0))
   ]
  )

(define-metafunction dada-type-system
  place-invalidated-by-action? : program env place action -> boolean

  [(place-invalidated-by-action? program env place action)
   (ty-invalidated-by-action? program env ty action)
   (where ty (place-ty program env place))
   ]
  )

(define-metafunction dada-type-system
  ty-invalidated-by-action? : program env ty action -> boolean

  [(ty-invalidated-by-action? program env int _) #f]

  [(ty-invalidated-by-action? program env (mode borrowed leases ty) action)
   (any? (mode-invalidated-by-action? program env mode action)
         (leases-invalidated-by-action? program env leases action)
         (ty-invalidated-by-action? program env ty action))]

  [(ty-invalidated-by-action? program env (mode c params) action)
   (any? (mode-invalidated-by-action? program env mode action)
         (params-invalidated-by-action? program env params action))]

  [(ty-invalidated-by-action? program env (mode p) action)
   (mode-invalidated-by-action? program env mode action)]
  
  [(ty-invalidated-by-action? program env (dt params) action)
   (params-invalidated-by-action? program env mode action)]
        
  )

(define-metafunction dada-type-system
  mode-invalidated-by-action? : program env mode action -> boolean

  [(mode-invalidated-by-action? program env my _) #f]
  [(mode-invalidated-by-action? program env (shared leases) action)
   (leases-invalidated-by-action? program env leases action)
   ])

(define-metafunction dada-type-system
  params-invalidated-by-action? : program env params action -> boolean

  [(params-invalidated-by-action? program env (param ...) action)
   (any? (param-invalidated-by-action? program env param action) ...)])

(define-metafunction dada-type-system
  param-invalidated-by-action? : program env param action -> boolean

  [(param-invalidated-by-action? program env ty action) (ty-invalidated-by-action? program env ty action)]
  [(param-invalidated-by-action? program env leases lease) (leases-invalidated-by-action? program env ty lease)])

(define-metafunction dada-type-system
  leases-invalidated-by-action? : program env leases action -> boolean

  [(leases-invalidated-by-action? program env (lease ...) action)
   (any? (lease-invalidated-by-action? lease action) ...)])

;; lease-references-lease lease_1 lease_2
;;
;; True if revoking `lease_2` means `lease_1` is revoked.
(define-metafunction dada-type-system
  lease-invalidated-by-action? : lease action -> boolean

  ;; Examples:
  ;;
  ;; If we have a borrowed lease on `a.b`, and the user reads `a.b.c`, then our borrowed lease is revoked.
  ;; If we have a borrowed lease on `a.b.c`, and the user reads `a.b`, then our borrowed lease is revoked.
  ;; If we have a borrowed lease on `a.b.c`, and the user reads `a.d`, then our borrowed lease is unaffected.
  [(lease-invalidated-by-action? (borrowed place_1) (read place_2)) (places-overlapping? place_1 place_2)]
  
  ;; If we have a shared/borrowed lease on `a.b`, and the user writes to `a.b.c`, then our shared lease is revoked.
  ;; If we have a shared/borrowed lease on `a.b.c`, and the user writes to `a.b`, then our shared lease is revoked.
  [(lease-invalidated-by-action? (_ place_1) (write place_2)) (places-overlapping? place_1 place_2)]

  ;; If we have a shared lease on `a.b`, and the user reads some memory (no matter what), our lease is unaffected.
  [(lease-invalidated-by-action? (shared place_1) (read place_2)) #f]
  )

(redex-let*
 dada-type-system
 [(program program_test)
  (ty_my_string (term (my String ())))
  (ty_sh_string (term ((shared ((shared (the-string)))) String ())))
  (env_sh (term ((maybe-init ((the-string) (sh-string)))
                 (def-init ((the-string) (sh-string)))
                 (vars (
                        (the-string ty_my_string)
                        (sh-string ty_sh_string)
                        )))))

  (ty_my_pair (term (my Pair (ty_my_string ty_sh_string))))
  (ty_sh_from_pair_string (term ((shared  ((shared (pair)))) String ())))
  (env_pair (term ((maybe-init ((the-string) (pair) (from-pair)))
                   (def-init ((the-string) (pair) (from-pair)))
                   (vars (
                          (the-string ty_my_string)
                          (pair ty_my_pair)
                          (from-pair ty_sh_from_pair_string)
                          )))))

  (ty_b_string (term (my borrowed ((borrowed (the-string))) ty_my_string)))
  (env_b (term ((maybe-init ((the-string) (b-string)))
                (def-init ((the-string) (b-string)))
                (vars (
                       (the-string ty_my_string)
                       (b-string ty_b_string)
                       )))))

  (lease_x (term (shared (the-string))))
  (action_x (term (read (the-string))))
  ]

 (test-equal-terms (lease-invalidated-by-action? lease_x action_x) #f)
 
 ;; reading the-string does not invalidate shares
 (test-equal-terms (definitely-initialized-places (terminate-lease program env_sh read (the-string))) ((the-string) (sh-string)))

 ;; writing the-string *does* invalidate shares
 (test-equal-terms (definitely-initialized-places (terminate-lease program env_sh write (the-string))) ((the-string)))

 ;; reading the-string does invalidate borrows
 (test-equal-terms (definitely-initialized-places (terminate-lease program env_b read (the-string))) ((the-string)))

 ;; writing the-string does invalidate shares
 (test-equal-terms (definitely-initialized-places (terminate-lease program env_b write (the-string))) ((the-string)))

 ;; writing the-string invalidates pair, which invalidates from-pair
 (test-equal-terms (definitely-initialized-places (terminate-lease program env_pair write (the-string))) ((the-string)))
 )

;; (place-extensions program env place) -> places
;;
;; Given a place like `a.b`, yields all legal extensions
;; (e.g., `a.b.c`, a.b.d`) that add a single field.
(define-metafunction dada-type-system
  place-extensions : program env place -> places
  [(place-extensions program env place)
   ((x f ... f_place) ...)
   (where ty_place (place-ty program env place))
   (where (f_place ...) (field-names program ty_place))
   (where (x f ...) place)
   ]

  )

;; (place-prefix-in place places) -> place
;;
;; Yields the prefix of `place` found in `places`.
(define-metafunction dada-type-system
  place-prefix-in : place places -> place
  [(place-prefix-in place places)
   (x_prefix f_prefix ...)
   (where (place_0 ... (x_prefix f_prefix ...) place_1 ...) places)
   (where (x_prefix f_prefix ... f_other ...) place)
   ]
  )

;; (any-places-overlapping? places)
;;
;; Checks if any two places in `places` are overlapping.
(define-metafunction dada-type-system
  any-places-overlapping? : places -> boolean
  [(any-places-overlapping? places)
   #t
   (where (place_0 ... place_a place_2 ... place_b place_3 ...) places)
   (side-condition (term (places-overlapping? place_a place_b)))
   ]
  [(any-places-overlapping? places) #f]
  )

;; partition-places place places -> (places_overlapping places_other)
;;
;; Splits a list of places `places` into those places that overlap with `place`
;; and those that do not.
(define-metafunction dada-type-system
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

;; missing-fields? places_present places_all
;;
;; True if the set of places in `places_present` represents all
;; the fields cited in `places_all`. At all times the former
;; must be a subset of the latter. This is used when extending
;; and expanding places, so e.g. `places_all` might be something like
;; `p.x` and `p.y` (for a point `p`), and `places_present` some subset
;; of those.
(define-metafunction dada
  missing-fields? : places_present places_all -> boolean
  #:pre ,(subset? (term places_present) (term places_all))
  [(missing-fields? places_1 places_2)
   ,(proper-subset? (term places_1) (term places_2))
   ]
  )

;; is-minimal? program env places
;;
;; A set of places `places` is *minimal* if there is no place `p`
;; where `places` contains (`p.f1` ... `p.fN`) for each field `f1...fN`
;; that can extend the place `p`. In that case, `places` should just
;; contain `p`.
(define-metafunction dada-type-system
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
(define-metafunction dada-type-system
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

;; minimize-places-fix program env place places
;;
;; Helper function: place is a prefix that was just added to places.
;; Check whether we need to recursively minimize. This occurs
;; when you e.g. adding `a.b.c` let's us find that `a.b` is fully initialized,
;; which in turn may mean that `a` is fully initialized.
(define-metafunction dada-type-system
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

;; (initialize-place program env place places_in places_out)
;;
;; Given a list of places (`places_in`) that is either maybe
;; or definitely initialized, adds `place` to that list, adjusting
;; the list as needed to ensure the `any-places-overlapping?` property
;; is maintained.
(define-judgment-form dada-type-system
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

  [(where env_tl (terminate-lease program env write place))
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

  [(where env_tl (terminate-lease program env write place))
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
                     (a-pair ty_my_pair))))))
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
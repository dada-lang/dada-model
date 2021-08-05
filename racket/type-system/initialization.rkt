#lang racket
(require racket/set redex "../grammar.rkt" "../util.rkt" "lang.rkt" "terminate-lease.rkt")
(provide definitely-initialized?
         maybe-initialized?
         definitely-not-initialized?
         env-with-initialized-place
         places-with-deinitialized-place
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

;; (place-extensions program env place) -> places
;;
;; Given a place like `a.b`, yields all legal extensions
;; (e.g., `a.b.c`, a.b.d`) that add a single field.
(define-metafunction dada-type-system
  place-extensions : program env place -> places
  [(place-extensions program env place)
   ((x f ... f_place) ...)
   (where ty_place (place-type program env place))
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
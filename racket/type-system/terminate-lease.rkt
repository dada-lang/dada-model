#lang racket
(require redex "../grammar.rkt" "../util.rkt" "lang.rkt")
(provide terminate-lease)

;; terminate-leave program env lease-kind place -> env
;;
;; Removes any places from the list of "definitely initialized"
;; places whose types may reference (lease-kind place).
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
  terminate-lease : program env action-kind place -> env

  [(terminate-lease program env action-kind place)
   (with-definitely-initialized-places places_remaining env)
   (where places_def_init (definitely-initialized-places env))
   (where action (action-kind place))
   (where places_remaining (terminate-lease-places program env action places_def_init))
   ]
  )

(define-metafunction dada-type-system
  terminate-lease-places : program env action places -> places

  [(terminate-lease-places program env action places_def_init)
   (terminate-lease-places-fix program env places_remaining0 places_invalidated)
   (where (places_invalidated places_remaining0) ,(partition-list (λ (place) (term (place-invalidated-by-action program env ,place action))) (term places_def_init)))
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
  place-invalidated-by-action : program env place action -> boolean

  [(place-invalidated-by-action program env place action)
   (ty-invalidated-by-action program env ty action)
   (where ty (place-type program env place))
   ]
  )

(define-metafunction dada-type-system
  ty-invalidated-by-action : program env ty action -> boolean

  [(ty-invalidated-by-action program env int _) #f]

  [(ty-invalidated-by-action program env (mode borrowed leases ty) action)
   (any (mode-invalidated-by-action program env mode action)
        (leases-invalidated-by-action program env leases action)
        (ty-invalidated-by-action program env ty action))]

  [(ty-invalidated-by-action program env (mode c params) action)
   (any (mode-invalidated-by-action program env mode action)
        (params-invalidated-by-action program env params action))]

  [(ty-invalidated-by-action program env (mode p) action)
   (mode-invalidated-by-action program env mode action)]
  
  [(ty-invalidated-by-action program env (dt params) action)
   (params-invalidated-by-action program env mode action)]
        
  )

(define-metafunction dada-type-system
  mode-invalidated-by-action : program env mode action -> boolean

  [(mode-invalidated-by-action program env my _) #f]
  [(mode-invalidated-by-action program env (shared leases) action)
   (leases-invalidated-by-action program env leases action)
   ])

(define-metafunction dada-type-system
  params-invalidated-by-action : program env params action -> boolean

  [(params-invalidated-by-action program env (param ...) action)
   (any (param-invalidated-by-action program env param action) ...)])

(define-metafunction dada-type-system
  param-invalidated-by-action : program env param action -> boolean

  [(param-invalidated-by-action program env ty action) (ty-invalidated-by-action program env ty action)]
  [(param-invalidated-by-action program env leases lease) (leases-invalidated-by-action program env ty lease)])

(define-metafunction dada-type-system
  leases-invalidated-by-action : program env leases action -> boolean

  [(leases-invalidated-by-action program env (lease ...) action)
   (any (lease-invalidated-by-action lease action) ...)])

;; lease-references-lease lease_1 lease_2
;;
;; True if revoking `lease_2` means `lease_1` is revoked.
(define-metafunction dada-type-system
  lease-invalidated-by-action : lease action -> boolean

  ;; Examples:
  ;;
  ;; If we have a borrowed lease on `a.b`, and the user reads `a.b.c`, then our borrowed lease is revoked.
  ;; If we have a borrowed lease on `a.b.c`, and the user reads `a.b`, then our borrowed lease is revoked.
  ;; If we have a borrowed lease on `a.b.c`, and the user reads `a.d`, then our borrowed lease is unaffected.
  [(lease-invalidated-by-action (borrowed place_1) (read place_2)) (places-overlapping place_1 place_2)]
  
  ;; If we have a shared/borrowed lease on `a.b`, and the user writes to `a.b.c`, then our shared lease is revoked.
  ;; If we have a shared/borrowed lease on `a.b.c`, and the user writes to `a.b`, then our shared lease is revoked.
  [(lease-invalidated-by-action (_ place_1) (write place_2)) (places-overlapping place_1 place_2)]

  ;; If we have a shared lease on `a.b`, and the user reads some memory (no matter what), our lease is unaffected.
  [(lease-invalidated-by-action (shared place_1) (read place_2)) #f]
  )

(redex-let*
 dada-type-system
 [(program (term ([(String (class () ()))
                   (Pair (class ((A out) (B out)) ((a (my A)) (b (my B)))))
                   (Vec (class ((E out)) ()))
                   (Fn (class ((A in) (R out)) ()))
                   (Cell (class ((T inout)) ()))
                   ]
                  [(Point (data () ()))
                   (Option (data ((T out)) ()))
                   ]
                  [])))
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

 (test-equal-terms (lease-invalidated-by-action lease_x action_x) #f)
 
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

#lang racket
(require redex
         data/order
         "../util.rkt"
         "../grammar.rkt"
         "lang.rkt"
         "substitution.rkt")
(provide unscope-vars-in-lease)

(define-metafunction dada-type-system
  ;; unscope-vars-in-leases ...
  unscope-vars-in-leases : program_in env_in leases_in xs_dead -> leases_out

  [(unscope-vars-in-leases program env (lease_in ...) xs_dead)
   (lease_out0 ... ...)
   (where ((lease_out0 ...) ...) ((unscope-vars-in-lease program env lease_in xs_dead) ...))
   ]
  )

(define-metafunction dada-type-system
  ;; unscope-vars-in-lease ...
  ;;
  ;;
  unscope-vars-in-lease : program_in env_in lease_in xs_dead -> leases_out

  [(unscope-vars-in-lease program env (lease-kind place) xs_dead)
   ((lease-kind place))
   (where #t (place-in-scope? place xs_dead))]

  [(unscope-vars-in-lease program env (_ place) xs_dead)
   (unscope-vars-in-perms program env perms xs_dead)
   (where (perms c _) (place-ty program env place))]

  [(unscope-vars-in-lease program env (_ place) xs_dead)
   (unscope-vars-in-perms program env perms xs_dead)
   (where (perms p) (place-ty program env place))]

  [;; Lease parameters are always in scope
   (unscope-vars-in-lease program env p xs_dead)
   (p)
   ]

  [;; Special atomic lease is always in scope
   (unscope-vars-in-lease program env atomic xs_dead)
   (atomic)
   ]

  [; Everything else expires
   (unscope-vars-in-lease program env lease xs_dead)
   (expired)]
  )

(define-metafunction dada-type-system
  ;; unscope-vars-in-perms ...
  ;;
  ;;
  unscope-vars-in-perms : program_in env_in perms_in xs_dead -> leases_out

  [(unscope-vars-in-perms program env (shared leases_in) xs_dead)
   (unscope-vars-in-leases program env leases_in xs_dead)]

  [(unscope-vars-in-perms program env (lent leases_in) xs_dead)
   (unscope-vars-in-leases program env leases_in xs_dead)]

  [(unscope-vars-in-perms program env my xs_dead) (expired)]

  [(unscope-vars-in-perms program env our xs_dead) (expired)]
  )

(define-metafunction dada-type-system
  ;; place-in-scope? place xs_dead
  ;;
  ;; False if `place` begins with a variable from `xs_dead`
  place-in-scope? : place xs -> boolean

  [(place-in-scope? (x f ...) (x_0 ... x x_1 ...)) #f]

  [(place-in-scope? place xs) #t]

  )

(module+ test

  (define-syntax-rule
    (test-out-of-scope ((x-term ty-term) ...) leases-in leases-out)
    (redex-let*
     dada-type-system
     [(env (term (test-env (x-term ty-term) ...)))]
     (test-equal-terms (unscope-vars-in-leases
                        program_test
                        env
                        leases-in
                        (x-term ...))
                       leases-out)
     ))

  (define-syntax-rule
    (test-out-of-scope-err ((x-term ty-term) ...) leases-in)
    (redex-let*
     dada-type-system
     [(env (term (test-env (x-term ty-term) ...)))]
     (test-equal-terms (unscope-vars-in-leases
                        program_test
                        env
                        leases-in
                        (x-term ...))
                       (expired))
     ))

  (test-out-of-scope-err
   ; fn(x: our Character) -> shared(x) String
   ; becomes expired
   [(x (our Character ()))]
   ((shared (x))))

  (test-out-of-scope
   ; fn<lease alpha>(x: shared(alpha) Character) -> shared(x) String
   ; becomes shared(alpha) String
   [(x ((shared (alpha)) Character ()))]
   ((shared (x)))
   (alpha))

  (test-out-of-scope
   ; fn<lease alpha>(x: shared(alpha atomic) Character) -> shared(x) String
   ; becomes shared(alpha atomic) String
   [(x ((shared (alpha atomic)) Character ()))]
   ((shared (x)))
   (alpha atomic))

  (test-out-of-scope
   ; fn<lease alpha>(x: shared(alpha) Character, y: shared(x) String) -> shared(y) String
   ; becomes shared(alpha) String
   ;
   ; Tests that we handle "fixed point"
   [(x ((shared (alpha)) Character ()))
    (y ((shared ((shared (x)))) String ()))]
   ((shared (y)))
   (alpha))

  (test-out-of-scope
   ; fn<lease alpha>(x: shared(alpha) Character, y: shared(x) String) -> shared(y) String
   ; becomes shared(alpha) String
   ;
   ; Tests that we handle "fixed point"
   [(x ((shared (alpha)) Character ()))
    (y ((shared ((shared (x)))) String ()))]
   ((shared (y)))
   (alpha))

  (test-out-of-scope
   ; fn<lease alpha, type T>(x: shared(alpha) T, y: shared(x) String) -> shared(y) String
   ; becomes shared(alpha) String
   ;
   ; Tests that we handle "fixed point"
   [(x ((shared (alpha)) T))
    (y ((shared ((shared (x)))) String ()))]
   ((shared (y)))
   (alpha))

  (test-out-of-scope
   ; fn<lease alpha, type T>(x: lent(beta) T) -> lent(x) String
   ; becomes lent(beta) String
   ;
   ; Tests that we handle "fixed point"
   [(x ((lent (beta)) T))]
   ((lent (x)))
   (beta))

  (test-out-of-scope
   ; fn<lease alpha, type T>(x: lent(beta) T) -> shared(x) String
   ; becomes shared(beta) String
   ;
   ; Tests that we handle "fixed point"
   [(x ((lent (beta)) T))]
   ((shared (x)))
   (beta))

  (test-out-of-scope
   ; fn<lease alpha, type T>(x: shared(alpha) T) -> lent(x) String
   ;
   ; It's not clear how one could *define* this function, since getting something
   ; lent from something shared is not legal, but the signature is harmless.
   [(x ((shared (alpha)) T))]
   ((lent (x)))
   (alpha))

  (test-out-of-scope-err
   ; fn(x: my String) -> shared(x) String
   ; yields an error -- how can't have something shared from something owned.
   [(x (my String ()))]
   ((shared (x))))

  (test-out-of-scope-err
   ; fn(x: our String) -> shared(x) String
   ; yields an error -- how can't have something shared from something owned.
   [(x (our String ()))]
   ((shared (x))))

  (test-out-of-scope-err
   ; fn(x: my p) -> shared(x) String
   ; yields an error -- how can't have something shared from something owned.
   [(x (my p))]
   ((shared (x))))

  (test-out-of-scope-err
   ; fn(x: my String) -> lent(x) String
   ; yields an error -- how can't have something lent from something owned.
   [(x (my String ()))]
   ((lent (x))))
  )

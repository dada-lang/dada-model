#lang racket
(require redex data/order "../util.rkt" "../grammar.rkt" "lang.rkt")
(provide limit-scoping-in-lease)

(define-metafunction dada-type-system
  ;; limit-scoping-in-leases ...
  limit-scoping-in-leases : program_in env_in leases_in xs_live -> leases_out

  [(limit-scoping-in-leases program env (lease_in ...) xs_live)
   (lease_out0 ... ...)
   (where ((lease_out0 ...) ...) ((limit-scoping-in-lease program env lease_in xs_live) ...))
   ]
  )

(define-metafunction dada-type-system
  ;; limit-scoping-in-lease ...
  ;;
  ;; 
  limit-scoping-in-lease : program_in env_in lease_in xs_live -> leases_out

  [(limit-scoping-in-lease program env (lease-kind place) xs_live)
   ((lease-kind place))
   (where #t (place-in-scope? place xs_live))]
  
  [(limit-scoping-in-lease program env (shared place) xs_live)
   (limit-scoping-in-mode program env mode xs_live)
   (where (mode c _) (place-ty program env place))]

  [(limit-scoping-in-lease program env (shared place) xs_live)
   (limit-scoping-in-mode program env mode xs_live)
   (where (mode p) (place-ty program env place))]

  [; A shared lease that references borrowed content lives as long as that
   ; borrow is still alive.
   (limit-scoping-in-lease program env (shared place) xs_live)
   (limit-scoping-in-leases program env leases xs_live)
   (where (my borrowed leases _) (place-ty program env place))
   ]

  [; A shared lease that references shared borrowed content lives as long
   ; as that sharing is active.
   (limit-scoping-in-lease program env (shared place) xs_live)
   (limit-scoping-in-leases program env leases_sh xs_live)
   (where ((shared leases_sh) borrowed _ _) (place-ty program env place))
   ]

  [; A borrowed lease that references borrowed content lives as long as that
   ; borrow is still alive.
   (limit-scoping-in-lease program env (borrowed place) xs_live)
   (limit-scoping-in-leases program env leases xs_live)
   (where (my borrowed leases _) (place-ty program env place))
   ]

  [; A borrowed lease that references shared content is invalid-- expire.
   (limit-scoping-in-lease program env (borrowed place) xs_live)
   (expired)
   (where ((shared _) borrowed leases _) (place-ty program env place))
   ]

  [; Ints own their content, so borrows from them expire when they go out of scope.
   (limit-scoping-in-lease program env (borrowed place) xs_live)
   (expired)
   (where int (place-ty program env place))
   ]

  [; Data types own their content, so borrows from them expire when they go out of scope.
   (limit-scoping-in-lease program env (borrowed place) xs_live)
   (expired)
   (where (dt _) (place-ty program env place))]

  [;; Lease parameters are always in scope
   (limit-scoping-in-lease program env p xs_live)
   (p)
   ]

  [;; Special atomic lease is always in scope
   (limit-scoping-in-lease program env atomic xs_live)
   (atomic)
   ]
  
  )

(define-metafunction dada-type-system
  ;; limit-scoping-in-mode ...
  ;;
  ;; 
  limit-scoping-in-mode : program_in env_in mode_in xs_live -> leases_out

  [(limit-scoping-in-mode program env (shared leases_in) xs_live)
   (limit-scoping-in-leases program env leases_in xs_live)]

  [(limit-scoping-in-mode program env my xs_live) (expired)]
  )

(define-metafunction dada-type-system
  ;; place-in-scope? place xs_live
  ;;
  ;; True if `place` begins with a variable from `xs_live`
  place-in-scope? : place xs -> boolean

  [(place-in-scope? (x f ...) (x_0 ... x x_1 ...))
   #t]

  [(place-in-scope? place xs) #f]
  
  )

(redex-let*
 dada-type-system
 [(program program_test)]

 (define-syntax-rule
   (test-out-of-scope ((x-term ty-term) ...) leases-in leases-out)
   (redex-let*
    dada-type-system
    [(env (term (test-env (x-term ty-term) ...)))]
    (test-equal-terms (limit-scoping-in-leases
                       program
                       env
                       leases-in
                       ())
                      leases-out)
    ))

 (define-syntax-rule
   (test-out-of-scope-err ((x-term ty-term) ...) leases-in)
   (redex-let*
    dada-type-system
    [(env (term (test-env (x-term ty-term) ...)))]
    (test-equal-terms (limit-scoping-in-leases
                       program
                       env
                       leases-in
                       ())
                      (expired))
    ))

 (test-out-of-scope
  ; fn(x: our Character) -> shared(x) String
  ; becomes our String
  [(x (our Character ()))]
  ((shared (x)))
  ())

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
  ; fn<lease alpha, type T>(x: shared(alpha) borrowed(beta) T) -> shared(x) String
  ; becomes shared(alpha) String
  ;
  ; Tests that we handle "fixed point"
  [(x ((shared (alpha)) borrowed (beta) (my T)))]
  ((shared (x)))
  (alpha))

 (test-out-of-scope
  ; fn<lease alpha, type T>(x: my borrowed(beta) T) -> borrowed(x) String
  ; becomes borrowed(beta) String
  ;
  ; Tests that we handle "fixed point"
  [(x (my borrowed (beta) (my T)))]
  ((borrowed (x)))
  (beta))

 (test-out-of-scope-err
  ; fn<lease alpha, type T>(x: shared(alpha) borrowed(beta) T) -> borrowed(x) String
  ; yields an error -- how can't have something borrowed from something shared!
  [(x ((shared (alpha)) borrowed (beta) (my T)))]
  ((borrowed (x))))

 (test-out-of-scope-err
  ; fn(x: my String) -> shared(x) String
  ; yields an error -- how can't have something shared from something owned.
  [(x (my String ()))]
  ((shared (x))))

 (test-out-of-scope-err
  ; fn(x: my p) -> shared(x) String
  ; yields an error -- how can't have something shared from something owned.
  [(x (my p))]
  ((shared (x))))
 )
 

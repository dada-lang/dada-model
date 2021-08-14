#lang racket
(require redex data/order "../util.rkt" "../grammar.rkt" "lang.rkt")
(provide limit-scoping-in-leases)

(define-judgment-form dada-type-system
  ;; limit-scoping-in-leases ...
  ;;
  ;; 
  #:mode (limit-scoping-in-leases I I I I O)
  #:contract (limit-scoping-in-leases program_in env_in leases_in xs_live leases_out)

  [(limit-scoping-in-lease program env lease_in xs_live (lease_out0 ...)) ...
   (where leases_out (lease_out0 ... ...))
   --------------------
   (limit-scoping-in-leases program env (lease_in ...) xs_live leases_out)]
  )

(define-judgment-form dada-type-system
  ;; limit-scoping-in-leases ...
  ;;
  ;; 
  #:mode (limit-scoping-in-lease I I I I O)
  #:contract (limit-scoping-in-lease program_in env_in lease_in xs_live leases_out)

  [(place-in-scope place xs_live)
   --------------------
   (limit-scoping-in-lease program env (lease-kind place) xs_live ((lease-kind place)))]
  
  [(place-out-of-scope place xs_live)
   (where (mode c _) (place-ty program env place))
   (limit-scoping-in-mode program env mode xs_live leases_out)
   --------------------
   (limit-scoping-in-lease program env (shared place) xs_live leases_out)]

  [(place-out-of-scope place xs_live)
   (where (mode borrowed _ _) (place-ty program env place))
   (limit-scoping-in-mode program env mode xs_live leases_out)
   --------------------
   (limit-scoping-in-lease program env (shared place) xs_live leases_out)]

  [(place-out-of-scope place xs_live)
   (where (mode p) (place-ty program env place))
   (limit-scoping-in-mode program env mode xs_live leases_out)
   --------------------
   (limit-scoping-in-lease program env (shared place) xs_live leases_out)]

  [(place-out-of-scope place xs_live)
   (where (my borrowed leases _) (place-ty program env place))
   (limit-scoping-in-leases program env leases xs_live leases_out)
   --------------------
   (limit-scoping-in-lease program env (shared place) xs_live leases_out)]

  [(place-out-of-scope place xs_live)
   (where (my borrowed leases _) (place-ty program env place))
   (limit-scoping-in-leases program env leases xs_live leases_out)
   --------------------
   (limit-scoping-in-lease program env (borrowed place) xs_live leases_out)]

  [;; Lease parameters are always in scope
   --------------------
   (limit-scoping-in-lease program env p xs_live (p))]

  [;; Special atomic lease is always in scope
   --------------------
   (limit-scoping-in-lease program env atomic xs_live (atomic))]
  
  )

(define-judgment-form dada-type-system
  ;; limit-scoping-in-mode ...
  ;;
  ;; 
  #:mode (limit-scoping-in-mode I I I I O)
  #:contract (limit-scoping-in-mode program_in env_in mode_in xs_live leases_out)

  [(limit-scoping-in-leases program env leases_in xs_live leases_out)
   --------------------
   (limit-scoping-in-mode program env (shared leases_in) xs_live leases_out)]
  )

(define-judgment-form dada-type-system
  ;; place-in-scope place xs_live
  ;;
  ;; True if `place` begins with a variable from `xs_live`
  #:mode (place-in-scope I I)
  #:contract (place-in-scope place xs)

  [-------------------
   (place-in-scope (x f ...) (x_0 ... x x_1 ...))]
  
  )

(define-judgment-form dada-type-system
  ;; place-out-of-scope place xs_live
  ;;
  ;; True if `place` does not begin with a variable from `xs_live`
  #:mode (place-out-of-scope I I)
  #:contract (place-out-of-scope place xs)

  [(different-variables x x_live) ...
   -------------------
   (place-out-of-scope (x f ...) (x_live ...))]
  
  )

(define-judgment-form dada-type-system
  ;; place-out-of-scope place xs_live
  ;;
  ;; 
  #:mode (different-variables I I)
  #:contract (different-variables x x)

  [-------------------
   (different-variables x_!_0 x_!_0)]
  
  )
(redex-let*
 dada-type-system
 [(program program_test)]

 (define-syntax-rule
   (test-out-of-scope ((x-term ty-term) ...) leases-in leases-out)
   (redex-let*
    dada-type-system
    [(env (term (test-env (x-term ty-term) ...)))]
    (test-judgment-holds (limit-scoping-in-leases
                          program
                          env
                          leases-in
                          ()
                          leases-out))
    ))

 (define-syntax-rule
   (test-out-of-scope-err ((x-term ty-term) ...) leases-in)
   (redex-let*
    dada-type-system
    [(env (term (test-env (x-term ty-term) ...)))]
    (test-judgment-false (limit-scoping-in-leases
                          program
                          env
                          leases-in
                          ()
                          _))
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
 )
 

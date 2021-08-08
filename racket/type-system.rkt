#lang racket
(require redex "grammar.rkt" "util.rkt")
(require "type-system/lang.rkt" "type-system/initialization.rkt" "type-system/assignable.rkt" "type-system/mutability.rkt")
(provide (all-defined-out)
         (all-from-out "type-system/lang.rkt"))

;; expr-ty env_in expr_in ty_out env_out
;;
;; Computes the type of an expression in a given environment,
;; as well as the resulting environment for subsequent expressions.
(define-judgment-form dada-type-system
  #:mode (expr-ty I I I O O)
  #:contract (expr-ty program env expr ty env)

  ;; number
  ;;
  ;; Numbers always have type `int`.
  [--------------------------
   (expr-ty _ env_in number int env_in)]

  ;; (seq exprs)
  ;;
  ;; Sequences thread the environment through each expr,
  ;; and they discard intermediate values. Their type is
  ;; the type of the final value.
  [(exprs-types program env_in (expr_0 ... expr_n) (ty_0 ... ty_n) env_out)
   --------------------------
   (expr-ty program env_in (seq (expr_0 ... expr_n)) ty_n env_out)]

  ;; As a special case, empty sequences evaluate to 0.
  [--------------------------
   (expr-ty program env_in (seq ()) int env_in)]

  ;; (var (x ty) = expr)
  ;;
  ;; Introduce a new variable into the environment.
  [; First type the initializer
   (expr-ty program env_in expr_init ty_init env_init)

   ; For simplicity, an error to shadow variables
   (side-condition (term (not? (env-contains-var? env_init x))))

   ; The initializer must be assignable to `ty`
   (ty-assignable program ty_init ty_x)
   
   ; Introduce `x: ty_x` into the environment
   (env-with-initialized-place program (env-with-var env_init x ty_x) (x) env_out)
   --------------------------
   (expr-ty program env_in (var (x ty_x) = expr_init) int env_out)]

  ;; (set place = expr_value)
  ;;
  ;; Overwrite place
  [(expr-ty program env_in expr_value ty_value env_value)
   (ty-assignable program ty_value (place-ty program env_in place))
   (env-with-initialized-place program env_in place env_out)
   --------------------------
   (expr-ty program env_in (set place = expr_value) int env_out)]

  ;; (share place)
  ;;
  ;; Sharing a place:
  ;;
  ;; * Sharing qualifies as a read.
  ;; * The data must be "definitely-initialized".
  ;; * If we are sharing something that is already shared,
  ;;   then the resulting type doesn't change, and hence
  ;;   the reusing value is independent of `place`.
  ;; * But if we are sharing something owned, then we
  ;;   get back a `(shared place)` lease.
  [(side-condition (definitely-initialized? env_in place))
   (where leases ((shared place)))
   (where ty_place (place-ty program env_in place))
   (where ty_shared (share-ty program leases ty_place))
   (where env_out (terminate-lease program env_in read place))
   --------------------------
   (expr-ty program env_in (share place) ty_shared env_out)]

  ;; Giving an affine place makes it de-initialized
  [(side-condition (definitely-initialized? env_in place))   
   (where ty_place (place-ty program env_in place))
   (env-with-deinitialized-place program env_in place env_out)
   (is-affine-ty ty_place)
   --------------------------
   (expr-ty program env_in (give place) ty_place env_out)]

  ;; Giving a copy place does not
  [(side-condition (definitely-initialized? env_in place))   
   (where ty_place (place-ty program env_in place))
   (is-copy-ty ty_place)
   --------------------------
   (expr-ty program env_in (give place) ty_place env_in)]

  ;; (data-instance dt params exprs)
  ;;
  ;; Evaluates to a data instance.
  [(where generic-decls (datatype-generic-decls program dt))
   (where (ty_f0 ...) (datatype-field-tys program dt))
   (where (ty_f1 ...) ((subst-ty program generic-decls params ty_f0) ...))
   (exprs-types program env_in exprs_fields (ty_v ...) env_out)
   (ty-assignable program ty_v ty_f1) ...
   --------------------------
   (expr-ty program env_in (data-instance dt params exprs_fields) (dt params) env_out)]

  ;; (class-instance c params exprs)
  ;;
  ;; Evaluates to a (owned) class instance.
  [(where generic-decls (class-generic-decls program c))
   (where (ty_f0 ...) (class-field-tys program c))
   (where (ty_f1 ...) ((subst-ty program generic-decls params ty_f0) ...))
   (exprs-types program env_in exprs_fields (ty_v ...) env_out)
   (ty-assignable program ty_v ty_f1) ...
   --------------------------
   (expr-ty program env_in (class-instance c params exprs_fields) (my c params) env_out)]

  )

;; Computes the types of a series of expressions,
;; threading the environment through from one to the next.
(define-judgment-form
  dada-type-system
  #:mode (exprs-types I I I O O)
  #:contract (exprs-types program env exprs tys env)

  [--------------------------
   (exprs-types program env () () env)]

  [(expr-ty program env_in expr_0 ty_0 env_0)
   (exprs-types program env_0 (expr_1 ...) (ty_1 ...) env_1)
   --------------------------
   (exprs-types program env_in (expr_0 expr_1 ...) (ty_0 ty_1 ...) env_1)]
  )

(redex-let*
 dada-type-system
 [(program program_test)
  (env_empty env_empty)
  (ty_my_string (term (my String ())))
  (expr_let (term (seq ((var (s ty_my_string) = (class-instance String () ()))))))
  (ty_our_string (term ((shared ()) String ())))
  (ty_pair_of_strings (term (my Pair (ty_my_string ty_my_string))))
  (expr_new_string (term (class-instance String () ())))
  ]

   
 (test-equal-terms lease_x lease_x)
 
 (test-judgment-holds 
  (expr-ty
   program
   env_empty
   (seq ())
   int
   env_empty))

 (test-judgment-holds 
  (expr-ty
   program
   env_empty
   (data-instance Point () (22 44))
   (Point ())
   env_empty))

 (test-judgment-holds 
  (expr-ty
   program
   env_empty
   (class-instance String () ())
   (my String ())
   env_empty))

 (test-judgment-holds 
  (expr-ty
   program
   env_empty
   (class-instance Character () (22 (class-instance String () ()) 44))
   (my Character ())
   env_empty))

 ;; Fields in wrong order, doesn't type
 (test-judgment-false
  (expr-ty
   program
   env_empty
   (class-instance Character () ((class-instance String () ()) 22 44))
   _
   _))

 (test-judgment-holds
  (expr-ty
   program
   env_empty
   expr_let
   int
   env_empty))
 
 (test-judgment-holds
  (expr-ty
   program
   env_empty
   expr_let
   int
   ((maybe-init ((s))) (def-init ((s))) (vars ((s (my String ())))))))

 (test-judgment-holds
  (expr-ty
   program
   env_empty
   (seq (expr_let (share (s))))
   ((shared ((shared (s)))) String ())
   ((maybe-init ((s))) (def-init ((s))) (vars ((s (my String ())))))))

 (test-judgment-holds
  (expr-ty
   program
   env_empty
   (seq (expr_let (give (s))))
   (my String ())
   ((maybe-init ()) (def-init ()) (vars ((s (my String ())))))))

 (test-judgment-false
  (expr-ty
   program
   env_empty
   (seq (expr_let (give (s)) (share (s))))
   _
   _))

 (test-judgment-false
  (expr-ty
   program
   env_empty
   (seq (expr_let (give (s)) (give (s))))
   _
   _))

 (test-judgment-holds
  (expr-ty
   program
   env_empty
   (seq ((var (age int) = 22) (give (age)) (give (age))))
   int
   ((maybe-init ((age))) (def-init ((age))) (vars ((age int))))))

 (test-judgment-holds
  (expr-ty
   program
   env_empty
   (seq ((var (name ty_our_string) = (class-instance String () ())) (give (name)) (give (name))))
   (side-condition ty (equal? (term ty) (term ty_our_string)))
   (side-condition env (equal? (term env) (term ((maybe-init ((name))) (def-init ((name))) (vars ((name ty_our_string)))))))
   ))

 (test-judgment-false
  (expr-ty
   program
   env_empty
   (seq ((var (our-name ty_our_string) = (class-instance String () ())) (var (my-name ty_my_string) = (give (our-name)))))
   _
   _))

 )
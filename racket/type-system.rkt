#lang racket
(require redex
         "grammar.rkt"
         "util.rkt"
         "type-manip.rkt"
         "type-system/lang.rkt"
         "type-system/initialization.rkt"
         "type-system/assignable.rkt"
         "type-system/accessible.rkt"
         "type-system/initialization.rkt"
         "type-system/adjust-leases.rkt"
         "type-system/expired-leases-in-place.rkt"
         )
(provide expr-drop expr-ty
         (all-from-out "type-system/lang.rkt"))

(define-judgment-form dada-type-system
  ;; expr-drop env_in expr_in env_out
  ;;
  ;; Computes the type of an expression in a given environment,
  ;; as well as the resulting environment for subsequent expressions.
  #:mode (expr-drop I I I O)
  #:contract (expr-drop program env expr env)

  [(expr-ty program env_in expr _ env_expr)
   (where env_out (adjust-leases-in-env program env_expr drop-in-flight))
   --------------------------
   (expr-drop program env_in expr env_out)]

  )

(define-judgment-form dada-type-system
  ;; expr-into env_in expr_in ty env_out
  ;;
  ;; Checks that expr produces a value that can be stored into
  ;; a (freshly allocated) place whose type is `ty`. It is
  ;; important that `ty` is freshly allocated because its type
  ;; should be independent of `expr_in` being evaluated.
  ;;
  ;; Note that `(set)` requires its own subtle rules, because
  ;; this property does not hold.
  #:mode (expr-into I I I I O)
  #:contract (expr-into program env expr ty env)

  [; Convenience rule for things that don't care where they are stored
   (expr-ty program env_in expr ty_expr env_out)
   (ty-assignable program ty_expr ty_dest)
   --------------------------
   (expr-into program env_in expr ty_dest env_out)]

  )

(define-judgment-form dada-type-system
  ;; expr-ty env_in expr_in ty_out env_out
  ;;
  ;; Helper for expr-into: types expressions that do not care where they are being
  ;; stored (which is many of them).
  #:mode (expr-ty I I I O O)
  #:contract (expr-ty program env expr ty env)

  [;; number
   ;;
   ;; Numbers always have type `int`.
   --------------------------
   (expr-ty _ env_in number int env_in)]

  [;; (seq exprs)
   ;;
   ;; Sequences thread the environment through each expr,
   ;; and they discard intermediate values. Their type is
   ;; the type of the final value.
   (exprs-drop program env_in (expr_0 ...) env_0)
   (expr-ty program env_0 expr_n ty_n env_out)
   --------------------------
   (expr-ty program env_in (seq (expr_0 ... expr_n)) ty_n env_out)]
  
  [;; As a special case, empty sequences evaluate to 0.
   --------------------------
   (expr-ty program env_in (seq ()) int env_in)]

  [;; Atomic expressions are typed as normal, but with the
   ;; atomic flag set to true.
   ;;
   ;; FIXME: Are other effects required? For example,
   ;; converting the types of all local variables to
   ;; borrowed or something like that?
   (where atomic?_in (env-atomic env_in))
   (where env_atomic (env-with-atomic env_in (atomic)))
   (expr-ty program env_atomic expr ty env_expr)
   (where env_out (env-with-atomic env_expr atomic?_in))
   --------------------------
   (expr-ty program env_in (atomic expr) ty env_out)]

  [;; (var (x ty) = expr)
   ;;
   ;; Introduce a new variable into the environment.

   ; Evaluate `expr` and create a variable `x` that has the resulting
   ; type.
   (expr-into-fresh-var program env_in expr_init x env_x)

   ; Make `(x)` considered initialized
   (env-with-initialized-place program env_x (x) env_initialized)

   ; Check that `x` in the environment has a type compatible with declared
   ; type and upcast (FIXME -- maybe we should just have `var x = ...` and
   ; remove this?)
   (env-upcast program env_initialized x ty_x env_out) 
   --------------------------
   (expr-ty program env_in (var (x ty_x) = expr_init) int env_out)]

  [;; (set place = expr_value)
   ;;
   ;; Overwrite place
   (place-initializable env_in place)
   (expr-ty program env_in expr_value ty_value env_value)
   
   ; Subtle: I think we want to determine the type of `place`
   ; *after* `expr_value` is evaluated, lest that
   ; evaluation disturbs or changes the type.
   (where ty_place (place-ty program env_value place))
   (ty-assignable program ty_value ty_place)

   ; Subtle: for the same reason, I think we want to check for
   ; expired leases afterwards. This aims to prevent programs
   ; like `x.y = give x`. This does however imply that the op sem will
   ; evaluate `place` after evaluating `expr_value`, which could
   ; potentially be observable given atomic sections?
   (no-expired-leases-traversing-place program env_value place)

   ; Similarly: check that `place` is write-accessible with final
   ; environment.
   (write-accessible program env_value place (env-atomic env_value))

   ; `place` is now initialized.
   (env-with-initialized-place program env_value place env_place_init)
   (where env_initialized (adjust-leases-in-env program env_place_init (write place)))

   ; Adjust leases now that the in-flight value is stored into x
   (where env_out (adjust-leases-in-env program env_initialized (store-in-flight place)))
   --------------------------
   (expr-ty program env_in (set place = expr_value) int env_out)]
 
  [;; (share place)
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
   (side-condition (definitely-initialized? env_in place))
   (read-accessible program env_in place (env-atomic env_in))
   (atomic-required-for-read? program env_in place (lease ...))
   (where leases ((shared place) lease ...))
   (where ty_place (place-ty program env_in place))
   (no-expired-leases-in-place program env_in place)
   (where ty_shared (share-ty program leases ty_place))
   (where env_out (adjust-leases-in-env program env_in (read place)))
   --------------------------
   (expr-ty program env_in (share place) ty_shared env_out)]

  [;; (lend place)
   ;;
   ;; Lending a place:
   ;;
   ;; * Requires that the location is both initialized and
   ;;   mutable.
   ;; * Yields a `borrowed T`
   (side-condition (definitely-initialized? env_in place))
   (write-accessible program env_in place (env-atomic env_in))
   (where leases ((borrowed place)))
   (where ty_place (place-ty program env_in place))
   (no-expired-leases-in-place program env_in place)
   (where ty_borrowed (my borrowed leases ty_place))
   (where env_out (adjust-leases-in-env program env_in (write place)))
   --------------------------
   (expr-ty program env_in (lend place) ty_borrowed env_out)]

  [;; Giving an affine place makes it de-initialized
   (side-condition (definitely-initialized? env_in place))
   (read-accessible program env_in place (env-atomic env_in))
   (where ty_place (place-ty program env_in place))
   (is-affine-ty ty_place)
   (no-expired-leases-in-place program env_in place)
   (place-uniquely-owns-its-location program env_in place)
   (where env_given (adjust-leases-in-env program env_in (give place)))
   (env-with-deinitialized-place program env_given place env_out)
   --------------------------
   (expr-ty program env_in (give place) ty_place env_out)]

  [;; Giving a copy place does not
   (side-condition (definitely-initialized? env_in place))
   (read-accessible program env_in place (env-atomic env_in))
   (side-condition (definitely-initialized? env_in place))
   (where ty_place (place-ty program env_in place))
   (no-expired-leases-in-place program env_in place)
   (is-copy-ty ty_place)
   --------------------------
   (expr-ty program env_in (give place) ty_place env_in)]

  [;; (data-instance dt params exprs)
   ;;
   ;; Evaluates to a data instance.
   (where generic-decls (datatype-generic-decls program dt))
   (where ((f ty_f0) ...) (datatype-field-var-decls program dt))
   (where (ty_f1 ...) ((subst-ty program generic-decls params ty_f0) ...))
   (exprs-into-fields program env_in exprs_fields ((f ty_f1) ...) env_out)
   --------------------------
   (expr-ty program env_in (data-instance dt params exprs_fields) (dt params) env_out)]

  [;; (class-instance c params exprs)
   ;;
   ;; Evaluates to a (owned) class instance.
   (where generic-decls (class-generic-decls program c))
   (where ((f ty_f0) ...) (class-field-var-decls program c))
   (where (ty_f1 ...) ((subst-ty program generic-decls params ty_f0) ...))
   (exprs-into-fields program env_in exprs_fields ((f ty_f1) ...) env_out)
   --------------------------
   (expr-ty program env_in (class-instance c params exprs_fields) (my c params) env_out)]

  )

(define-judgment-form dada-type-system
  ;; expr-into-fresh-var env expr x env_out
  ;;
  ;; Helper that types `expr` and adds a variable `x` to
  ;; the environment containing the resulting type.
  ;;
  ;; `x` is NOT considered initialized in the output environment.
  ;;
  ;; `x` must not yet exist in the environment.
  #:mode (expr-into-fresh-var I I I I O)
  #:contract (expr-into-fresh-var program env expr x env)

  [; Type the initializer
   (expr-ty program env_in expr ty_expr env_expr)

   ; Introduce `x` into the environment (uninitialized, thus far)
   (side-condition (term (not? (env-contains-var? env_expr x))))
   (where env_x (env-with-var env_expr (x ty_expr)))

   ; Adjust the leases to account for in-flight value being stored in `x`
   (where env_out (adjust-leases-in-env program env_x (store-in-flight (x))))
   --------------------------
   (expr-into-fresh-var program env_in expr x env_out)]
  )

(define-judgment-form dada-type-system
  ;; env-upcast program env x ty env_out
  ;;
  ;; Given an environment `env` containing a type `ty_x` for the
  ;; variable `x`, check that `ty_x` is assignable to `ty`
  ;; and then create `env_out` where `x: ty` instead.
  #:mode (env-upcast I I I I O)
  #:contract (env-upcast program env x ty env)

  [(where ((x_0 ty_0) ... (x ty_x) (x_1 ty_1) ...) (var-tys-in-env env_in))
   (ty-assignable program ty_x ty)
   (where env_out (env-with-var-tys env_in ((x_0 ty_0) ... (x ty) (x_1 ty_1) ...)))
   --------------------------
   (env-upcast program env_in x ty env_out)]
  )

(define-judgment-form dada-type-system
  ;; exprs-drop env_in exprs_in ty_out env_out
  ;;
  ;; Computes the type of an expression in a given environment,
  ;; as well as the resulting environment for subsequent expressions.
  #:mode (exprs-drop I I I O)
  #:contract (exprs-drop program env exprs env)

  [--------------------------
   (exprs-drop program env_in () env_in)]

  [(expr-drop program env_in expr_0 env_0)
   (exprs-drop program env_0 (expr_1 ...) env_1)
   --------------------------
   (exprs-drop program env_in (expr_0 expr_1 ...) env_1)]

  )

(define-judgment-form dada-type-system
  ;; Computes the types of a series of expressions,
  ;; threading the environment through from one to the next.
  #:mode (exprs-into-fields I I I I O)
  #:contract (exprs-into-fields program env exprs var-decls env)

  [(where ids_f (f ...))
   (where (x_temp ...) (fresh-temporaries program env_in exprs ids_f))
   (exprs-into-fresh-vars program env_in exprs (x_temp ...) env_exprs)
   (where env_gathered (adjust-leases-in-env program env_exprs (gather ((x_temp (in-flight f)) ...))))
   (where (ty_temp ...) ((var-ty env_gathered x_temp) ...))
   (ty-assignable program ty_temp ty) ...
   (env-without-temporaries env_gathered (x_temp ...) env_out)
   --------------------------
   (exprs-into-fields program env_in exprs ((f ty) ...) env_out)]
  )

(define-judgment-form dada-type-system
  ;; (exprs-into-fresh-vars program env exprs xs env)
  ;;
  ;; Evaluate `exprs` into a series of fresh variables `xs`.
  
  #:mode (exprs-into-fresh-vars I I I I O)
  #:contract (exprs-into-fresh-vars program env exprs xs env)

  [--------------------------
   (exprs-into-fresh-vars program env () () env)]

  [(expr-into-fresh-var program env_in expr_0 x_0 env_0)
   (exprs-into-fresh-vars program env_0 (expr_1 ...) (x_1 ...) env_1)
   --------------------------
   (exprs-into-fresh-vars program env_in (expr_0 expr_1 ...) (x_0 x_1 ...) env_1)]
  )

(define-judgment-form dada-type-system
  ;; (env-without-temporaries env xs env)
  ;;
  ;; Removes the variables `xs` from the list of environment variables.
  
  #:mode (env-without-temporaries I I O)
  #:contract (env-without-temporaries env_in xs_in env_out)

  ; Either: there are no temporaries, *or* the temporaries *were* present in the
  ; environment, but are not once we are done.
  #:inv ,(or (equal? (term xs_in) '())
             (and (not (equal? (variables-not-in (term env_in) (term xs_in)) (term xs_in)))
                  (equal? (variables-not-in (term env_out) (term xs_in)) (term xs_in))))

  [(where env_out (env-with-var-tys env (var-tys-without-temporaries (var-tys-in-env env) xs)))
   --------------------------
   (env-without-temporaries env xs env_out)]

  )

(define-metafunction dada-type-system
  ;; (env-without-temporaries env xs env)
  ;;
  ;; Removes the variables `xs` from the list of environment variables.
  var-tys-without-temporaries : var-tys xs -> var-tys

  [; Base case of empty lits
   (var-tys-without-temporaries () xs)
   ()]
  
  [; Remove `(x_v0 ty_v0)` if `x_v0` appears in `xs`
   (var-tys-without-temporaries ((x_v0 ty_v0) (x_v1 ty_v1) ...) (name xs (_ ... x_v0 _ ...)))
   (var-tys-without-temporaries ((x_v1 ty_v1) ...) xs)]

  [; Otherwise, keep `(x_v0 ty_v0)`
   (var-tys-without-temporaries ((x_v0 ty_v0) (x_v1 ty_v1) ...) xs)
   ((x_v0 ty_v0) (x_r ty_r) ...)
   (where ((x_r ty_r) ...) (var-tys-without-temporaries ((x_v1 ty_v1) ...) xs))]

  )

(define-judgment-form dada-type-system
  ;; enter-atomic-section env_in env_atomic
  ;;
  ;; Creates a new environment that is inside an atomic section
  ;;
  ;; FIXME: Are other effects required? For example,
  ;; converting the types of all local variables to
  ;; borrowed or something like that?
  #:mode (enter-atomic-section I O)
  #:contract (enter-atomic-section env env)

  [--------------------------
   (enter-atomic-section env_in (env-with-atomic env_in (atomic)))]

  )

(define-judgment-form dada-type-system
  ;; exit-atomic-section env_before env_after env_out
  ;;
  ;; Given
  ;;
  ;; * the environment `env_before` before entering the atomic section
  ;; * the environment `env_after` after executing the atomic section
  ;;
  ;; creates a new environment `env_out` that corresponds to having
  ;; exited the atomic section.
  #:mode (exit-atomic-section I I O)
  #:contract (exit-atomic-section env env env)

  [(where env_out (env-with-atomic env_after (env-atomic env_before)))
   --------------------------
   (exit-atomic-section env_before env_after env_out)]

  )

(module+ test
  (redex-let*
   dada-type-system
   [(ty_my_string (term (my String ())))
    (expr_var (term (var (s ty_my_string) = (class-instance String () ()))))
    (ty_our_string (term ((shared ()) String ())))
    (ty_pair_of_strings (term (my Pair (ty_my_string ty_my_string))))
    (expr_new_string (term (class-instance String () ())))
    ]

   
   (test-equal-terms lease_x lease_x)
 
   (test-judgment-holds 
    (expr-ty
     program_test
     env_empty
     (seq ())
     int
     env_empty))

   (test-judgment-holds 
    (expr-ty
     program_test
     env_empty
     (data-instance Point () (22 44))
     (Point ())
     env_empty))

   (test-judgment-holds 
    (expr-ty
     program_test
     env_empty
     (class-instance String () ())
     (my String ())
     env_empty))

   (test-judgment-holds 
    (expr-ty
     program_test
     env_empty
     (class-instance Character () (22 (class-instance String () ()) 44))
     (my Character ())
     env_empty))

   ;; Fields in wrong order, doesn't type
   (test-judgment-false
    (expr-ty
     program_test
     env_empty
     (class-instance Character () ((class-instance String () ()) 22 44))
     _
     _))

   (test-judgment-holds
    (expr-ty
     program_test
     env_empty
     expr_var
     int
     env_empty))
 
   (test-judgment-holds
    (expr-ty
     program_test
     env_empty
     expr_var
     int
     ((maybe-init ((s))) (def-init ((s))) (vars ((s (my String ())))) ())))

   (test-judgment-holds
    (expr-drop
     program_test
     env_empty
     (seq (expr_var (share (s))))
     _
     ))

   (; test that after giving `s` away, it is no longer considered initialized
    test-judgment-holds
    (expr-drop
     program_test
     env_empty
     (seq (expr_var
           (var (tmp (my String ())) = (give (s)))))
     ((maybe-init ((tmp))) (def-init ((tmp))) (vars _) ())))

   (test-judgment-false
    (expr-ty
     program_test
     env_empty
     (seq (expr_var (give (s)) (share (s))))
     _
     _))

   (test-judgment-false
    (expr-ty
     program_test
     env_empty
     (seq (expr_var (give (s)) (give (s))))
     _
     _))

   (; for an integer, giving it away just makes copies
    test-judgment-holds
    (expr-drop
     program_test
     env_empty
     (seq ((var (age int) = 22)
           (var (tmp1 int) = (give (age)))
           (var (tmp2 int) = (give (age)))))
     ((maybe-init ((tmp2) (tmp1) (age))) (def-init ((tmp2) (tmp1) (age))) (vars _) ())))

   (test-judgment-holds
    (expr-drop
     program_test
     env_empty
     (seq ((var (name ty_our_string) = (class-instance String () ()))
           (var (tmp1 ty_our_string) = (give (name)))
           (var (tmp2 ty_our_string) = (give (name)))))
     ((maybe-init ((tmp2) (tmp1) (x_name))) ;; XXX can't write `name` because it's a keyword in patterns
      (def-init ((tmp2) (tmp1) (x_name)))
      (vars _)
      ())))

   (test-judgment-false
    (expr-ty
     program_test
     env_empty
     (seq ((var (our-name ty_our_string) = (class-instance String () ())) (var (my-name ty_my_string) = (give (our-name)))))
     _
     _))

   (test-judgment-false
    (expr-ty
     program_test
     (test-env (x (my Pair ((our String ()) ((shared (expired atomic)) String ())))))
     (give (x))
     _
     _))

   (test-judgment-holds
    (expr-ty
     program_test
     (test-env (x (my Pair ((our String ()) ((shared (expired atomic)) String ())))))
     (give (x a))
     _
     _))
 
   (test-judgment-false
    (expr-ty
     program_test
     (test-env (x (my Pair ((our String ()) ((shared (expired atomic)) String ())))))
     (give (x b))
     _
     _))
   )
  )
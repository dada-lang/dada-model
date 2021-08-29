#lang racket
(require redex
         "grammar.rkt"
         "type-system.rkt"
         "util.rkt"
         "opsem/lang.rkt")
(provide Dada
         eval-expr)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Well-typed

(define-metafunction Dada
  Value-of-type? : program Store Value ty -> boolean
  [(Value-of-type? program Store Value ty) #t]) ;TODO

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; "Medium" step semantics
;;
;; The function eval takes an expr and yields a Value directly,
;; which is a kind of of "big step" semantics, but our expressions
;; always terminate.

;; (eval-expr program store expr -> (Value Store))
;;
;; Evaluates an expression.
(define-metafunction Dada
  eval-expr : program_0 env_0 Store expr_0 -> (Value Store)

  ; the expression must be well-typed in the environment
  #:pre ,(judgment-holds (expr-ty program_0 env_0 expr_0 _ _))

  ;; Empty sequences: evaluate to 0
  [(eval-expr program env Store (seq)) (0 Store)]

  ;; Non-empty sequences: discard all values except the last
  [(eval-expr program env Store (seq (expr_0 ... expr_1)))
   (Value_1 Store_out)
   (where ((Value_0 ... Value_1) Store_out) (eval-exprs program env Store (expr_0 ... expr_1)))]

  ;; Numbers: evaluate to themselves
  [(eval-expr program env Store number) (number Store)]

  ;; var x = expr: evaluates to 0 but has side-effects
  ;;
  ;; Goes wrong if `x` is already on the stack or the value
  ;; doesn't match `ty`.
  [(eval-expr program env Store (var x = expr_init))
   (0 Store_out)
   (where (ty_init _) (ty-expr-in-env program env expr_init))
   (where (Value_init Store_init) (eval-expr program env Store expr_init))
   (where Store_out (declare-variable program env Store_init x ty_init Value_init))]

  [;; assert-ty place-at-rest : ty
   ;;
   ;; Just evaluates to 0.
   (eval-expr program env Store (assert-ty place-at-rest : ty))
   (0 Store)
   ]

  [;; expr : ty
   ;;
   ;; Upcast has no real effect.
   (eval-expr program env Store (expr : ty))
   (eval-expr program env Store expr)
   ]

  ;; give place: fetches place and returns it. If place is affine,
  ;; this will "move" place (FIXME: NYI).
  [(eval-expr program env Store (give place))
   ((read Store place) Store)]

  ;; data-instance: evaluate their fields, then create a data-instance
  [(eval-expr program env Store_in (data-instance dt params exprs_in))
   ((my dt ((f_c Value_f) ...)) Store_out)
   (where (f_c ...) (datatype-field-names program dt))
   (where ((Value_f ...) Store_out) (eval-exprs program env Store_in exprs_in))]

  ;; class-instance: evaluate their fields, then create a class instance.
  ;;
  ;; It will initially be a "my" value (note that it may be transparently
  ;; upcast into a shared mode).
  [(eval-expr program env Store_in (class-instance c params exprs_in))
   ((my c ((f_c Value_f) ...)) Store_out)
   (where (f_c ...) (class-field-names program c))
   (where ((Value_f ...) Store_out) (eval-exprs program Store_in exprs_in))]
  )

(define-metafunction Dada
  ;; declare-variable
  ;;
  ;; Defines the value of a new variable x and returns the new store
  ;;
  ;; Goes wrong if there is already a variable named `x` in scope
  declare-variable : program_0 env_0 Store_0 x_0 ty_0 Value_0 -> Store
  #:pre (all? (Value-of-type? program_0 Store_0 Value_0 ty_0)
              (fresh-var? Store_0 x_0))
  
  [(declare-variable program env Store x ty Value)
   (with-stack-entry (x Value) Store)
   ])

(define-metafunction Dada
  ;; clear-place
  ;;
  ;; Defines the value of a new variable x and returns the new store
  ;;
  ;; Goes wrong if there is already a variable named `x` in scope
  clear-place : program env Store place-at-rest -> Store
  
  [(clear-place program env Store place-at-rest)
   ()
   ])

(define-metafunction Dada
  ;; eval-exprs
  ;;
  ;; Evaluate a sequence of expressions, threading the store along
  ;; with them (and adjusting the environment).
  eval-exprs : program env Store exprs -> ((Value ...) Store)
  [(eval-exprs program env Store ()) (() Store)]
  [(eval-exprs program env Store (expr_0 expr_1 ...))
   ((Value_0 Value_1 ...) Store_1)
   (where (Value_0 Store_0) (eval-expr program env Store expr_0))
   (where (ty_0 env_0) (ty-expr-in-env program env expr_0))
   (where #t (assert (Value-of-type? program Store Value_0 ty_0)))
   (where ((Value_1 ...) Store_1) (eval-exprs program env_0 Store_0 (expr_1 ...)))]
  )



(define-metafunction Dada
  ; Convert the typing judgment into a metafunction
  ty-expr-in-env : program env expr -> (ty env)
  [(ty-expr-in-env program env expr)
   (ty_0 env_0)
   (where/error ((ty_0 env_0)) ,(judgment-holds (expr-ty program env expr ty_out env_out) (ty_out env_out)))
   ])

(define-term Store_empty
  ((stack ())
   (heap ())
   (ref-table ())))

(module+ test
  (redex-let*
   Dada
   [(program
     (term (; classes:
            []
            ; structs:
            [(some-struct (data () [(f0 int) (f1 int)]))]
            ; methods:
            []
            )))
    (env (term (test-env)))
    ]
   (test-match-terms Dada (eval-expr program env Store_empty (seq (22 44 66))) (66 Store_empty))
   (test-match-terms Dada (eval-expr program env Store_empty (data-instance some-struct () (22 44))) ((my some-struct ((f0 22) (f1 44))) Store_empty))
   (test-match-terms Dada (eval-expr program env Store_empty (var my-var = 22)) (0 ((stack ((my-var 22))) (heap ()) (ref-table ()))))
   (test-match-terms Dada (eval-expr program env Store_empty (seq ((var my-var = 22) (give (my-var))))) (22 Store_out))
   ))

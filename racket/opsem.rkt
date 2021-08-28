#lang racket
(require redex
         "grammar.rkt"
         "type-system.rkt"
         "util.rkt")
(provide (all-defined-out))

;; Convention: uppercase names are things that only exist at runtime
(define-extended-language Dada dada-type-system
  (Store (Stack Heap Ref-table))
  (Stack (stack Stack-values))
  (Stack-values (Stack-value ...))
  (Stack-value (x Value))
  (Heap (heap Heap-values))
  (Heap-values (Heap-value ...))
  (Heap-value (Address Value))
  (Ref-table (ref-table Ref-counts))
  (Ref-counts (Ref-count ...))
  (Ref-count (Address number))
  (Value (box Address) Instance)
  (Instance
   (class-instance Identity c Field-values)
   (data-instance dt Field-values)
   number)
  (Field-values (Field-value ...))
  (Field-value (f Value))
  (Address variable-not-otherwise-mentioned)
  (Identity shared my (our Address) expired))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic memory access metafunctions

(define-metafunction Dada
  the-stack : Store -> Stack-values
  [(the-stack ((stack Stack-values) _ _)) Stack-values])

;; `(with-stack-entry (x Value) Store)` returns a new `Store` with `x` assigned to `Value`.
;;
;; The expectation is that `x` is not already on the stack.
(define-metafunction Dada
  with-stack-entry : Stack-value Store -> Store
  [(with-stack-entry Stack-value_0 ((stack (Stack-value_1 ...)) Heap Ref-table))
   ((stack (Stack-value_0 Stack-value_1 ...)) Heap Ref-table)])

(define-metafunction Dada
  the-heap : Store -> Heap-values
  [(the-heap (_ (heap Heap-values) _)) Heap-values])

(define-metafunction Dada
  the-ref-counts : Store -> Ref-counts
  [(the-ref-counts (_ _ (ref-table Ref-counts))) Ref-counts])

(define-metafunction Dada
  load-stack : Store x -> Value
  [(load-stack Store x)
   Value
   (where (_ ... (x Value) _ ...) (the-stack Store))
   ]
  )

;; True if there is no variable named `x`.
(define-metafunction Dada
  fresh-var? : Store x -> boolean
  [(fresh-var? Store x)
   #f
   (where (_ ... (x Value) _ ...) (the-stack Store))]
  [(fresh-var? Store x)
   #t])

(define-metafunction Dada
  load-heap : Store Address -> Value
  [(load-heap Store Address)
   Value
   (where (_ ... (Address Value) _ ...) (the-heap Store))]
  )

(define-metafunction Dada
  load-ref-count : Store Address -> number
  [(load-ref-count Store Address)
   number
   (where (_ ... (Address number) _ ...) (the-ref-counts Store))]
  )

(define-metafunction Dada
  load-field : Store Instance f -> Value
  [(load-field Store (class-instance _ _ (_ ... (f Value) _ ...)) f) Value]
  [(load-field Store (data-instance _ (_ ... (f Value) _ ...)) f) Value]
  )

(define-metafunction Dada
  deref : Store Value -> Instance
  [(deref Store (box Address)) (deref Store (load-heap Store Address))]
  [(deref Store Instance) Instance]
  )

(define-metafunction Dada
  read : Store place -> Value
  [(read Store (x f ...)) (read-fields Store (load-stack Store x) (f ...))]
  )

(define-metafunction Dada
  read-fields : Store Value (f ...) -> Value
  [(read-fields Store Value ()) Value]
  [(read-fields Store Value (f_0 f_1 ...)) (read-fields Store (load-field Store (deref Store Value) f_0) (f_1 ...))])

(define-metafunction Dada
  increment-ref-count : Store Address -> Store
  [(increment-ref-count (Stack Heap (ref-table (Ref-count_0 ... (Address number) Ref-count_1 ...))) Address)
   (Stack Heap (ref-table (Ref-count_0 ... (Address (increment number)) Ref-count_1 ...)))]
  )

(define-metafunction Dada
  increment : number -> number
  [(increment number) ,(+ 1 (term number))])

(module+ test
  (redex-let*
   Dada
   [(Store
     (term ((stack [(x0 22)
                    (x1 (box a0))
                    (x2 (data-instance some-struct ((f0 22) (f1 (box a0)))))
                    (x3 (box a1))])
            (heap [(a0 44)
                   (a1 (data-instance some-struct ((f0 22) (f1 (box a0)) (f2 (box a1)))))])
            (ref-table [(i0 66)]))))]
   (test-equal (term (load-stack Store x0)) 22)
   (test-equal (term (fresh-var? Store x0)) #f)
   (test-equal (term (fresh-var? Store not-a-var)) #t)
   (test-equal (term (load-stack Store x1)) (term (box a0)))
   (test-equal (term (load-heap Store a0)) 44)
   (test-equal (term (load-ref-count Store i0)) 66)
   (test-equal (term (deref Store (load-stack Store x1))) 44)
   (test-equal (term (read Store (x0))) 22)
   (test-equal (term (read Store (x1))) (term (box a0)))
   (test-equal (term (deref Store (read Store (x1)))) 44)
   (test-equal (term (read Store (x2 f0))) 22)
   (test-equal (term (deref Store (read Store (x2 f1)))) 44)
   (test-equal (term (deref Store (read Store (x3 f2 f2 f2 f2 f1)))) 44)
   (test-equal (term (load-ref-count (increment-ref-count Store i0) i0)) 67)
   )
  )

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
   ((data-instance dt ((f_c Value_f) ...)) Store_out)
   (where (f_c ...) (datatype-field-names program dt))
   (where ((Value_f ...) Store_out) (eval-exprs program env Store_in exprs_in))]

  ;; class-instance: evaluate their fields, then create a class instance.
  ;;
  ;; It will initially be a "my" value (note that it may be transparently
  ;; upcast into a shared mode).
  [(eval-expr program env Store_in (class-instance c params exprs_in))
   ((class-instance my c ((f_c Value_f) ...)) Store_out)
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
   (test-match-terms Dada (eval-expr program env Store_empty (data-instance some-struct () (22 44))) ((data-instance some-struct ((f0 22) (f1 44))) Store_empty))
   (test-match-terms Dada (eval-expr program env Store_empty (var my-var = 22)) (0 ((stack ((my-var 22))) (heap ()) (ref-table ()))))
   (test-match-terms Dada (eval-expr program env Store_empty (seq ((var my-var = 22) (give (my-var))))) (22 Store_out))
   ))

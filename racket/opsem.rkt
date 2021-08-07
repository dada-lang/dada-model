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
  (Ref-count (Identity number))
  (Value (box Address) Instance)
  (Instance
   (class-instance Identity c Field-values)
   (data-instance dt Field-values)
   number)
  (Field-values (Field-value ...))
  (Field-value (f Value))
  (Instance-identity Identity my shared)
  (Address variable-not-otherwise-mentioned)
  (Identity variable-not-otherwise-mentioned))

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
   (where ((x_0 Value_0) ... (x Value) (x_1 Value_1) ...) (the-stack Store))
   ]
  )

;; True if there is no variable named `x`.
(define-metafunction Dada
  fresh-var? : Store x -> boolean
  [(fresh-var? Store x)
   #f
   (where (Stack-value_0 ... (x Value) Stack-value_1 ...) (the-stack Store))]
  [(fresh-var? Store x)
   #t])

(define-metafunction Dada
  load-heap : Store Address -> Value
  [(load-heap Store Address) ,(cadr (assoc (term Address) (term (the-heap Store))))]
  )

(define-metafunction Dada
  load-ref-count : Store Identity -> number
  [(load-ref-count Store Identity) ,(cadr (assoc (term Identity) (term (the-ref-counts Store))))]
  )

(define-metafunction Dada
  load-field : Store Instance f -> Value
  [(load-field Store (class-instance _ _ Field-values) f) ,(cadr (assoc (term f) (term Field-values)))]
  [(load-field Store (data-instance _ Field-values) f) ,(cadr (assoc (term f) (term Field-values)))]
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

(define (assoc-update key value l)
  (match (car l)
    [(list k _) #:when (eq? k key) (cons (list key value) (cdr l))]
    [v (cons v (assoc-update key value (cdr l)))]))

(define-metafunction Dada
  increment-ref-count : Store Identity -> Store
  [(increment-ref-count (Stack Heap (ref-table Ref-counts)) Identity)
   (Stack Heap (ref-table ,(assoc-update (term Identity) (+ 1 (term (load-ref-count (Stack Heap (ref-table Ref-counts)) Identity))) (term Ref-counts))))]
  )

(test-equal (assoc-update 22 "z" '((44 "a") (22 "b") (66 "c"))) '((44 "a") (22 "z") (66 "c")))

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
  eval-expr : program Store expr -> (Value Store)

  ;; Empty sequences: evaluate to 0
  [(eval-expr program Store (seq)) (0 Store)]

  ;; Non-empty sequences: discard all values except the last
  [(eval-expr program Store (seq (expr_0 ... expr_1)))
   (Value_1 Store_out)
   (where ((Value_0 ... Value_1) Store_out) (eval-exprs program Store (expr_0 ... expr_1)))]

  ;; Numbers: evaluate to themselves
  [(eval-expr program Store number) (number Store)]

  ;; var x: ty = expr: evaluates to 0 but has side-effects
  ;;
  ;; Goes wrong if `x` is already on the stack or the value
  ;; doesn't match `ty`.
  [(eval-expr program Store (var (x ty) = expr_init))
   (0 Store_out)
   (where (Value_init Store_init) (eval-expr program Store expr_init))
   (where Store_out (declare-variable program Store_init x ty Value_init))]

  ;; give place: fetches place and returns it. If place is affine,
  ;; this will "move" place (FIXME: NYI).
  [(eval-expr program Store (give place))
   ((read Store place) Store)]

  ;; data-instance: evaluate their fields, then create a data-instance
  [(eval-expr program Store_in (data-instance dt params exprs_in))
   ((data-instance dt ((f_c Value_f) ...)) Store_out)
   (where (f_c ...) (datatype-field-names program dt))
   (where ((Value_f ...) Store_out) (eval-exprs program Store_in exprs_in))]

  ;; class-instance: evaluate their fields, then create a class instance.
  ;;
  ;; It will initially be a "my" value (note that it may be transparently
  ;; upcast into a shared mode).
  [(eval-expr program Store_in (class-instance c params exprs_in))
   ((class-instance my c ((f_c Value_f) ...)) Store_out)
   (where (f_c ...) (class-field-names program c))
   (where ((Value_f ...) Store_out) (eval-exprs program Store_in exprs_in))]
  )

;; Defines the value of a new variable x and returns the new store
;;
;; Goes wrong if there is already a variable named `x` in scope
(define-metafunction Dada
  declare-variable : program Store x ty Value -> Store
  [(declare-variable program Store x ty Value)
   (with-stack-entry (x Value) Store)
   (side-condition (term (fresh-var? Store x)))
   (side-condition (term (Value-of-type? program Store Value ty)))
   ])

(define-metafunction Dada
  eval-exprs : program Store exprs -> ((Value ...) Store)
  [(eval-exprs program Store ()) (() Store)]
  [(eval-exprs program Store (expr_0 expr_1 ...))
   ((Value_0 Value_1 ...) Store_1)
   (where (Value_0 Store_0) (eval-expr program Store expr_0))
   (where ((Value_1 ...) Store_1) (eval-exprs program Store_0 (expr_1 ...)))]
  )

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
  (Store_empty
   (term ((stack ())
          (heap ())
          (ref-table ()))))]
 (test-match-terms Dada (eval-expr program Store_empty (seq (22 44 66))) (66 Store_empty))
 (test-match-terms Dada (eval-expr program Store_empty (data-instance some-struct () (22 44))) ((data-instance some-struct ((f0 22) (f1 44))) Store_empty))
 (test-match-terms Dada (eval-expr program Store_empty (var (my-var int) = 22)) (0 ((stack ((my-var 22))) (heap ()) (ref-table ()))))
 (test-match-terms Dada (eval-expr program Store_empty (seq ((var (my-var int) = 22) (give (my-var))))) (22 Store_out))
 )

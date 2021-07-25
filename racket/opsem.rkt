#lang racket
(require redex)
(require "grammar.rkt")
(provide (all-defined-out))

;; Convention: uppercase names are things that only exist at runtime
(define-extended-language Dada dada
  (Store (Stack Heap Ref-counts))
  (Stack (stack Stack-value ...))
  (Stack-value (x Value))
  (Heap (heap Heap-value ...))
  (Heap-value (Address Value))
  (Ref-counts (ref-counts Ref-count ...))
  (Ref-count (Identity number))
  (Value (box Address) Data)
  (Data
   (class-instance Identity ty Field-values)
   (struct-instance ty Field-values)
   number)
  (Field-values (Field-value ...))
  (Field-value (f Value))
  (Address variable-not-otherwise-mentioned)
  (Identity variable-not-otherwise-mentioned))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic memory access metafunctions

(define-metafunction Dada
  the-stack : Store -> (Stack-value ...)
  [(the-stack ((stack Stack-value ...) _ _)) (Stack-value ...)])

;; `(with-stack-entry (x Value) Store)` returns a new `Store` with `x` assigned to `Value`.
;;
;; The expectation is that `x` is not already on the stack.
(define-metafunction Dada
  with-stack-entry : Stack-value Store -> Store
  [(with-stack-entry Stack-value_0 ((stack Stack-value_1 ...) Heap Ref-counts))
   ((stack Stack-value_0 Stack-value_1 ...) Heap Ref-counts)])

(define-metafunction Dada
  the-heap : Store -> (Heap-value ...)
  [(the-heap (_ (heap Heap-value ...) _)) (Heap-value ...)])

(define-metafunction Dada
  the-ref-counts : Store -> (Ref-count ...)
  [(the-ref-counts (_ _ (ref-counts Ref-count ...))) (Ref-count ...)])

(define-metafunction Dada
  load-stack : Store x -> Value
  [(load-stack Store x) ,(cadr (assoc (term x) (term (the-stack Store))))])

;; True if there is no variable named `x`.f
(define (fresh-var? Store x)
  (false? (assoc x (term (the-stack ,Store)))))

(define-metafunction Dada
  load-heap : Store Address -> Value
  [(load-heap Store Address) ,(cadr (assoc (term Address) (term (the-heap Store))))]
  )

(define-metafunction Dada
  load-ref-count : Store Identity -> number
  [(load-ref-count Store Identity) ,(cadr (assoc (term Identity) (term (the-ref-counts Store))))]
  )

(define-metafunction Dada
  load-field : Store Data f -> Value
  [(load-field Store (class-instance _ _ Field-values) f) ,(cadr (assoc (term f) (term Field-values)))]
  [(load-field Store (struct-instance _ Field-values) f) ,(cadr (assoc (term f) (term Field-values)))]
  )

(define-metafunction Dada
  deref : Store Value -> Data
  [(deref Store (box Address)) (deref Store (load-heap Store Address))]
  [(deref Store Data) Data]
  )

(define-metafunction Dada
  read : Store place -> Data
  [(read Store (x f ...)) (read-fields Store (deref Store (load-stack Store x)) (f ...))]
  )

(define-metafunction Dada
  read-fields : Store Data (f ...) -> Data
  [(read-fields Store Data ()) Data]
  [(read-fields Store Data (f_0 f_1 ...)) (read-fields Store (deref Store (load-field Store Data f_0)) (f_1 ...))])


(let [(store
       (term ((stack (x0 22)
                     (x1 (box a0))
                     (x2 (struct-instance some-struct ((f0 22) (f1 (box a0)))))
                     (x3 (box a1)))
              (heap (a0 44)
                    (a1 (struct-instance some-struct ((f0 22) (f1 (box a0)) (f2 (box a1))))))
              (ref-counts (i0 66)))))]
  (test-match Dada ty 'some-struct)
  (test-match Dada Field-values '((f0 22)))
  (test-match Dada Value '(struct-instance some-struct ((f0 22))))
  (test-match Dada Store store)
  (test-equal (term (load-stack ,store x0)) 22)
  (test-equal (fresh-var? store 'x0) #f)
  (test-equal (fresh-var? store 'not-a-var) #t)
  (test-equal (term (load-stack ,store x1)) (term (box a0)))
  (test-equal (term (load-heap ,store a0)) 44)
  (test-equal (term (load-ref-count ,store i0)) 66)
  (test-equal (term (deref ,store (load-stack ,store x1))) 44)
  (test-equal (term (read ,store (x0))) 22)
  (test-equal (term (read ,store (x1))) 44)
  (test-equal (term (read ,store (x2 f0))) 22)
  (test-equal (term (read ,store (x2 f1))) 44)
  (test-equal (term (read ,store (x3 f2 f2 f2 f2 f1))) 44)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Well-typed

(define-metafunction Dada
  Value-of-type? : program Store Value ty -> boolean
  [(Value-of-type? program Store Value ty) #t]) ;TODO

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Big step semantics

(define-metafunction Dada
  eval : program Store expr -> (Value Store)

  ;; Sequences: discard all values except the last
  [(eval program Store (seq expr))
   (eval program Store expr)]
  [(eval program Store (seq expr_0 expr_1 ...))
   ,(match (term (eval program Store expr_0))
      [(list _ Store_0) (term (eval program ,Store_0 (seq expr_1 ...)))])]

  ;; Numbers: evaluate to themselves
  [(eval program Store number) (number Store)]

  ;; let x: ty = expr: evaluates to 0 but has side-effects
  ;;
  ;; Goes wrong if `x` is already on the stack or the value
  ;; doesn't match `ty`.
  [(eval program Store (let (x ty) = expr_init))
   ,(match (term (eval program Store expr_init))
      [(list Value_init Store_init)
       (term (0 (let-variable program ,Store_init x ty ,Value_init)))])]


  ;; my place: fetches place and returns it. If place is affine,
  ;; this will "move" place (FIXME: NYI).
  [(eval program Store (my place))
   ((read Store place) Store)]

  ;; Struct-instances: evaluate their fields, then create a struct-instance
  [(eval program Store (struct-instance s (expr ...)))
   (eval-struct-instance
    program
    s
    (struct-named program s)
    (eval-exprs program Store (expr ...)))]
  )

;; Defines the value of a new variable x and returns the new store
;;
;; Goes wrong if there is already a variable named `x` in scope
(define-metafunction Dada
  let-variable : program Store x ty Value -> Store
  [(let-variable program Store x ty Value)
   (with-stack-entry (x Value) Store)
   (side-condition (fresh-var? (term Store) (term x)))
   (side-condition (term (Value-of-type? program Store Value ty)))
   ])

(define-metafunction Dada
  eval-exprs : program Store (expr ...) -> ((Value ...) Store)
  [(eval-exprs program Store (expr ...))
   (eval-exprs-helper program Store () (expr ...))])

(define-metafunction Dada
  eval-exprs-helper : program Store (Value ...) (expr ...) -> ((Value ...) Store)
  [(eval-exprs-helper program Store (Value ...) ()) ((Value ...) Store)]
  [(eval-exprs-helper program Store (Value ...) (expr_0 expr_1 ...))
   ,(match (term (eval program Store expr_0))
      [(list Value_0 Store_0) (term (eval-exprs-helper program ,Store_0 (Value ... ,Value_0) (expr_1 ...)))])])

;; Helper function that "zips" together the field names and values.
;; I can't figure out how to use redex-let or I would probably just do this inline.
(define-metafunction Dada
  eval-struct-instance : program s struct-definition ((Value ...) Store) -> (Value Store)
  [(eval-struct-instance program s (struct ((f _) ...)) ((Value ...) Store))
   ((struct-instance s ((f Value) ...)) Store)])

(let [(program
       (term (; classes:
              []
              ; structs:
              [(some-struct (struct [(f0 int) (f1 int)]))]
              ; methods:
              []
              )))
      (empty-store
       (term ((stack)
              (heap)
              (ref-counts))))]
  (test-equal (car (term (eval ,program ,empty-store (seq 22 44 66)))) 66)
  (test-equal (car (term (eval ,program ,empty-store (struct-instance some-struct (22 44))))) '(struct-instance some-struct ((f0 22) (f1 44))))
  (test-equal (car (term (eval ,program ,empty-store (seq (let (x int) = 22) (my (x)))))) 22)
  )

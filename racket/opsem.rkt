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

(define-metafunction Dada
  the-heap : Store -> (Heap-value ...)
  [(the-heap (_ (heap Heap-value ...) _)) (Heap-value ...)])

(define-metafunction Dada
  the-ref-counts : Store -> (Ref-count ...)
  [(the-ref-counts (_ _ (ref-counts Ref-count ...))) (Ref-count ...)])

(define-metafunction Dada
  load-stack : Store x -> Value
  [(load-stack Store x) ,(cadr (assoc (term x) (term (the-stack Store))))])

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
;; Big step semantics

(define-metafunction Dada
  eval : program Store expr -> Value

  ;; Sequences: discard all values except the last
  [(eval program Store (seq expr))
   (eval program Store expr)]
  [(eval program Store (seq expr_0 expr_1 ...))
   ,(let [(Value_0 (term (eval program Store expr_0)))]
      (term (eval program Store (seq expr_1 ...))))]

  ;; Numbers: evaluate to themselves
  [(eval program Store number) number]

  ;; Struct-instances: evaluate their fields, then create a struct-instance
  [(eval program Store (struct-instance s (expr ...)))
   (eval-struct-instance
    program
    Store
    s
    (struct-named program s)
    ((eval program Store expr) ...))]
  )

;; Helper function that "zips" together the field names and values.
;; I can't figure out how to use redex-let or I would probably just do this inline.
(define-metafunction Dada
  eval-struct-instance : program Store s struct-definition (Value ...) -> Value
  [(eval-struct-instance program Store s (struct ((f _) ...)) (Value ...))
   (struct-instance s ((f Value) ...))])

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
  (test-equal (term (eval ,program ,empty-store (seq 22 44 66))) 66)
  (test-equal (term (eval ,program ,empty-store (struct-instance some-struct (22 44)))) '(struct-instance some-struct ((f0 22) (f1 44))))
  )

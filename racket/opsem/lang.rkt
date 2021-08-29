#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         "../grammar.rkt"
         "../type-system.rkt"
         "../util.rkt")
(provide (all-defined-out))

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
  (Value (box Opt-shared Address) Unboxed-value)
  (Unboxed-value Aggregate number)
  (Aggregate (Identity id Field-values))
  (Field-values (Field-value ...))
  (Field-value (f Value))
  (Address variable-not-otherwise-mentioned)
  (Identity shared my (our Address) expired)
  (Opt-shared () (shared))
  )

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
  load-field : Store Unboxed-value f -> Value
  [(load-field Store (Identity id (_ ... (f Value) _ ...)) f) Value]
  )

(define-metafunction Dada
  deref : Store Value -> Unboxed-value
  [(deref Store (box _ Address)) (deref Store (load-heap Store Address))]
  [(deref Store Unboxed-value) Unboxed-value]
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
                    (x1 (box() a0))
                    (x2 (my some-struct ((f0 22) (f1 (box() a0)))))
                    (x3 (box() a1))])
            (heap [(a0 44)
                   (a1 (my some-struct ((f0 22) (f1 (box() a0)) (f2 (box() a1)))))])
            (ref-table [(i0 66)]))))]
   (test-equal (term (load-stack Store x0)) 22)
   (test-equal (term (fresh-var? Store x0)) #f)
   (test-equal (term (fresh-var? Store not-a-var)) #t)
   (test-equal (term (load-stack Store x1)) (term (box() a0)))
   (test-equal (term (load-heap Store a0)) 44)
   (test-equal (term (load-ref-count Store i0)) 66)
   (test-equal (term (deref Store (load-stack Store x1))) 44)
   (test-equal (term (read Store (x0))) 22)
   (test-equal (term (read Store (x1))) (term (box() a0)))
   (test-equal (term (deref Store (read Store (x1)))) 44)
   (test-equal (term (read Store (x2 f0))) 22)
   (test-equal (term (deref Store (read Store (x2 f1)))) 44)
   (test-equal (term (deref Store (read Store (x3 f2 f2 f2 f2 f1)))) 44)
   (test-equal (term (load-ref-count (increment-ref-count Store i0) i0)) 67)
   )
  )

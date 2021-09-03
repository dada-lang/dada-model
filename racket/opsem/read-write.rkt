#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         "../grammar.rkt"
         "../type-system.rkt"
         "../util.rkt"
         "lang.rkt")
(provide (all-defined-out))

(define-metafunction Dada
  load-heap : Store Address -> Value
  [(load-heap Store Address)
   Value
   (where (_ ... (Address Value) _ ...) (the-heap Store))]
  )

(define-metafunction Dada
  load-field : Store Unboxed-value f -> Value
  [(load-field Store (Identity id (_ ... (f Value) _ ...)) f) Value]
  )

(define-metafunction Dada
  deref : Store Value -> Unboxed-value
  [(deref Store (_ box Address)) (deref Store (load-heap Store Address))]
  [(deref Store Unboxed-value) Unboxed-value]
  )

(define-metafunction Dada
  read : Store place -> Value
  [(read Store (x f ...)) (read-fields Store (load-stack Store x) (f ...))]
  )

(define-metafunction Dada
  write : Store place Value_new -> Store
  [(write Store (x f ...) Value_new)
   Store_out
   (where/error Value_0 (load-stack Store x))
   (where/error (Store_1 Value_1) (write-fields Store Value_0 (f ...) Value_new))
   (where/error Store_out (with-stack-entry (x Value_1) Store_1))]
  )

(define-metafunction Dada
  read-fields : Store Value (f ...) -> Value
  [(read-fields Store Value ()) Value]
  [(read-fields Store Value (f_0 f_1 ...)) (read-fields Store (load-field Store (deref Store Value) f_0) (f_1 ...))])

(define-metafunction Dada
  write-fields : Store Value_old (f ...) Value_new -> (Store Value)
  
  [(write-fields Store Value_old () Value_new)
   (Store Value_new)]
  
  [(write-fields Store (Identity box Address) (f_0 f_1 ...) Value_new)
   (Store_2 (Identity box Address))
   (where/error Value_0 (load-heap Store Address))
   (where/error (Store_1 Value_1) (write-fields Store Value_0 (f_0 f_1 ...) Value_new))
   (where/error Store_2 (store-with-heap-entry Store_1 (Address Value_1)))]

  [(write-fields Store (Identity id (Field-value_0 ... (f_0 Value_f0_old) Field-value_1 ...)) (f_0 f_1 ...) Value_new)
   (Store_f0_new (Identity id (Field-value_0 ... (f_0 Value_f0_new) Field-value_1 ...)))
   (where/error (Store_f0_new Value_f0_new) (write-fields Store Value_f0_old (f_1 ...) Value_new))]
  
  )

(define-metafunction Dada
  load-stack : Store x -> Value
  [(load-stack Store x)
   Value
   (where (_ ... (x Value) _ ...) (the-stack Store))
   ]
  )

(module+ test
  (redex-let*
   Dada
   [(Stack (term (stack [(x0 22)
                         (x1 ((my i0) box a0))
                         (x2 ((my i0) some-struct ((f0 22) (f1 ((my i0) box a0)))))
                         (x3 ((my i0) box a1))])))
    (Ref-mappings (term [(i0 66)]))
    (Store
     (term (Stack
            (heap [(a0 44)
                   (a1 ((my i0) some-struct ((f0 22) (f1 ((my i0) box a0)) (f2 ((my i0) box a1)))))])
            (ref-table Ref-mappings))))]
   (test-equal (term (load-stack Store x0)) 22)
   (test-equal (term (fresh-var? Store x0)) #f)
   (test-equal (term (fresh-var? Store not-a-var)) #t)
   (test-equal (term (load-stack Store x1)) (term ((my i0) box a0)))
   (test-equal (term (load-heap Store a0)) 44)
   (test-equal (term (deref Store (load-stack Store x1))) 44)
   (test-equal (term (read Store (x0))) 22)
   (test-equal (term (read Store (x1))) (term ((my i0) box a0)))
   (test-equal (term (deref Store (read Store (x1)))) 44)
   (test-equal (term (read Store (x2 f0))) 22)
   (test-equal (term (deref Store (read Store (x2 f1)))) 44)
   (test-equal (term (deref Store (read Store (x3 f2 f2 f2 f2 f1)))) 44)
   (test-equal-terms (read (write Store (x2 f0) 88) (x2)) ((my i0) some-struct ((f0 88) (f1 ((my i0) box a0)))))
   (test-equal-terms (read (write Store (x3 f0) 88) (x3)) ((my i0) box a1))
   (test-match-terms Dada (write Store (x3 f0) 88) ((stack _) (heap (_ ... (a1 ((my i0) some-struct ((f0 88) _ ...))) _ ...)) (ref-table _)))
   )
  )
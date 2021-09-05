#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         "../grammar.rkt"
         "../type-system.rkt"
         "../util.rkt"
         "lang.rkt")
(provide (all-defined-out))

(define-metafunction Dada
  ;; load-stack
  ;;
  ;; Read the Value for a given variable from the stack.
  load-stack : Store x -> Value
  [(load-stack Store x)
   Value
   (where (_ ... (x Value) _ ...) (the-stack Store))
   ]
  )

(define-metafunction Dada
  ;; store-heap
  ;;
  ;; Update the value stored at Address, without changing its ref-count.
  store-heap : Store Address Unboxed-value -> Store
  [(store-heap Store Address Unboxed-value)
   (store-with-heap-entry Store (Address (box Ref-count Unboxed-value)))
   (where/error Ref-count (load-ref-count Store Address))]
  )

(define-metafunction Dada
  load-field : Store Unboxed-value f -> Value
  [(load-field Store (id (_ ... (f Value) _ ...)) f) Value]
  )

(define-metafunction Dada
  ;; deref
  ;;
  ;; Derefs through any boxes
  deref : Store Unboxed-value -> Unboxed-value
  [(deref Store (_ box Address)) (deref Store (load-heap Store Address))]
  [(deref Store Unboxed-value) Unboxed-value]
  )

(define-metafunction Dada
  read : Store place -> Value
  [(read Store (x f ...)) (read-fields Store (load-stack Store x) (f ...))]
  )

(define-metafunction Dada
  read-fields : Store Value (f ...) -> Value
  [(read-fields Store Value ()) Value]
  [(read-fields Store Value (f_0 f_1 ...))
   (read-fields Store (load-field Store (deref Store Value) f_0) (f_1 ...))])

(define-metafunction Dada
  write : Store place Value_new -> Store
  
  [(write Store (x f ...) Value_new)
   Store_out
   (where/error Value_0 (load-stack Store x))
   (where/error (Value_1 Store_1) (write-fields Store Value_0 (f ...) Value_new))
   (where/error Store_out (store-with-stack-mapping Store_1 (x Value_1)))]
  )

(define-metafunction Dada
  write-fields : Store Unboxed-value_old (f ...) Value_new -> (Unboxed-value Store)
  
  [(write-fields Store _ () Value_new)
   (Value_new Store)]
  
  [(write-fields Store (Ownership box Address) (f_0 f_1 ...) Value_new)
   ((Ownership box Address) Store_2)
   (where/error Unboxed-value_0 (load-heap Store Address))
   (where/error (Unboxed-value_1 Store_1) (write-fields Store Unboxed-value_0 (f_0 f_1 ...) Value_new))
   (where/error Store_2 (store-heap Store_1 Address Unboxed-value_1))]

  [(write-fields Store (id (Field-value_0 ... (f_0 Value_f0_old) Field-value_1 ...)) (f_0 f_1 ...) Value_new)
   ((id (Field-value_0 ... (f_0 Value_f0_new) Field-value_1 ...)) Store_f0_new)
   (where/error (Value_f0_new Store_f0_new) (write-fields Store Value_f0_old (f_1 ...) Value_new))]
  
  )

(module+ test
  (redex-let*
   Dada
   [(Stack-mappings (term [(x0 (my box an-int))
                           (x1 (my box struct-1))
                           (x2 (my box struct-2))]))
    (Store
     (term (Stack-mappings
            [(an-int (box 3 22))
             (another-int (box 1 44))
             (struct-1 (box 1 (some-struct [(f0 (my box an-int)) (f1 (my box struct-2))])))
             (struct-2 (box 2 (another-struct [(f0 66)])))])))
    ]
   
   (test-equal-terms (deref Store (load-stack Store x0))
                     22)
   (test-equal-terms (fresh-var? Store x0)
                     #f)
   (test-equal-terms (fresh-var? Store not-a-var)
                     #t)
   (test-equal-terms (load-stack Store x1)
                     (my box struct-1))
   (test-equal-terms (deref Store (load-stack Store x1))
                     (some-struct [(f0 (my box an-int)) (f1 (my box struct-2))]))
   (test-equal-terms (deref Store (read Store (x1 f0)))
                     22)
   (test-equal-terms (read (write Store (x1 f0) (my box another-int)) (x1 f0))
                     (my box another-int))

   (test-equal-terms (read Store (x2 f0))
                     66)
   (test-equal-terms (read (write Store (x2 f0) 88) (x2 f0))
                     88)
   
   )
  )
#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         "../grammar.rkt"
         "../type-system.rkt"
         "../util.rkt"
         "lang.rkt"
         "clone.rkt")
(provide read-place
         write-place
         share-place)

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
  [(load-field Store (_ (_ ... (f Value) _ ...)) f) Value]
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
  read-place : Store place -> Value
  [(read-place Store (x f ...)) (read-fields Store (load-stack Store x) (f ...))]
  )

(define-metafunction Dada
  read-fields : Store Value (f ...) -> Value
  [(read-fields Store Value ()) Value]
  [(read-fields Store Value (f_0 f_1 ...))
   (read-fields Store (load-field Store (deref Store Value) f_0) (f_1 ...))])

(define-metafunction Dada
  write-place : Store place Value_new -> Store
  
  [(write-place Store (x f ...) Value_new)
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

  [(write-fields Store (Aggregate-id (Field-value_0 ... (f_0 Value_f0_old) Field-value_1 ...)) (f_0 f_1 ...) Value_new)
   ((Aggregate-id (Field-value_0 ... (f_0 Value_f0_new) Field-value_1 ...)) Store_f0_new)
   (where/error (Value_f0_new Store_f0_new) (write-fields Store Value_f0_old (f_1 ...) Value_new))]
  
  )

(define-metafunction Dada
  share-place : Store place -> (Value Store)
  
  [(share-place Store place)
   (share-value Store Value_0)
   (where/error Value_0 (read-place Store place))]
  )

(define-metafunction Dada
  share-value : Store Value -> (Value Store)

  [(share-value Store Value)
   (Value (clone-value Store Value))
   (where #t (is-data? Store Value))]
  
  [(share-value Store (Ownership box Address))
   (((leased) box Address) Store)]
  
  )

(define-metafunction Dada
  is-data? : Store Unboxed-value -> boolean
  
  [(is-data? Store number) #t]
  
  [; Box: deref to see what's on the other side
   (is-data? Store (my box Address))
   (is-data? Store (load-heap Store Address))]

  [; Leased must be a class
   (is-data? Store ((leased) box Address))
   #f]

  [(is-data? Store ((data _) Field-values))
   #t]

  [(is-data? Store ((class _) Field-values))
   #f]
  
 
  
  )

(module+ test
  (redex-let*
   Dada
   [(Stack-mappings (term [(x0 (my box an-int))
                           (x1 (my box struct-1))
                           (x2 (my box struct-2))
                           (x4 (my box class-1))]))
    (Store
     (term (Stack-mappings
            [(an-int (box 3 22))
             (another-int (box 1 44))
             (struct-1 (box 1 ((data some-struct) [(f0 (my box an-int)) (f1 (my box struct-2))])))
             (struct-2 (box 2 ((data another-struct) [(f0 66)])))
             (class-1 (box 1 ((class some-class) [(f0 88)])))])))
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
                     ((data some-struct) [(f0 (my box an-int)) (f1 (my box struct-2))]))
   (test-equal-terms (deref Store (read-place Store (x1 f0)))
                     22)
   (test-equal-terms (read-place (write-place Store (x1 f0) (my box another-int)) (x1 f0))
                     (my box another-int))

   (test-equal-terms (read-place Store (x2 f0))
                     66)
   (test-equal-terms (read-place (write-place Store (x2 f0) 88) (x2 f0))
                     88)
   (test-match-terms Dada (share-place Store (x0)) ((my box an-int) [_ (_ ... (an-int (box 4 22)) _ ...)]))
   (test-equal-terms (share-place Store (x2 f0)) (66 Store))
   (test-equal-terms (share-place Store (x4)) (((leased) box class-1) Store))
   )
  )
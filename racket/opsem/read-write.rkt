#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         "../grammar.rkt"
         "../type-system.rkt"
         "../util.rkt"
         "lang.rkt"
         "clone.rkt"
         "stack.rkt"
         "heap.rkt"
         "lease.rkt")

(provide read-place
         write-place
         share-place
         lend-place)

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
  ;; read-place
  ;;
  ;; Reads the value stored at the given place.
  ;;
  ;; Returns the value along with the set of leases that were traversed to reach it.
  read-place : Store place -> (Value Leases Store)
  
  #;[(read-place Store place)
   ()
   (where 22 ,(pretty-print (term ("read-place" Store place))))]
  
  [(read-place Store (x f ...)) (read-fields Store () (var-in-store Store x) (f ...))]
  )

(define-metafunction Dada
  read-fields : Store Leases Unboxed-value (f ...) -> (Value Leases Store)

  #;[(read-fields Store Leases Unboxed-value (f ...))
   ()
   (where 22 ,(pretty-print (term ("read-fields" Store Leases Unboxed-value (f ...)))))]
  
  [(read-fields Store Leases Value ()) (Value Leases Store)]
  
  [(read-fields Store Leases (my box Address) (f_0 f_1 ...))
   (read-fields Store_read Leases Unboxed-value (f_0 f_1 ...))
   (where/error (Unboxed-value Store_read) (load-and-invalidate-heap Store my Address))
   ]

  [(read-fields Store Leases ((leased Lease) box Address) (f_0 f_1 ...))
   (read-fields Store_read (Lease) Unboxed-value (f_0 f_1 ...))
   (where shared (kind-of-lease Store Lease))
   (where/error (Unboxed-value Store_read) (load-and-invalidate-heap Store (leased Lease) Address))
   ]

  [(read-fields Store (Lease_in ...) ((leased Lease) box Address) (f_0 f_1 ...))
   (read-fields Store_read (Lease_in ... Lease) Unboxed-value (f_0 f_1 ...))
   (where borrowed (kind-of-lease Store Lease))
   (where/error (Unboxed-value Store_read) (load-and-invalidate-heap Store (leased Lease) Address))
   ]

  [(read-fields Store Leases Unboxed-value (f_0 f_1 ...))
   (read-fields Store Leases Unboxed-value_0 (f_1 ...))
   (where/error Unboxed-value_0 (load-field Store Unboxed-value f_0))])

(define-metafunction Dada
  ;; load-and-invalidate-heap
  ;;
  ;; Reads the value stored at the given place.
  ;;
  ;; Returns the value along with the set of leases that were traversed to reach it.
  load-and-invalidate-heap : Store Ownership Address -> (Unboxed-value Store)
  
  [(load-and-invalidate-heap Store Ownership Address)
   (Unboxed-value Store_out)
   (where/error Unboxed-value (load-heap Store Address))
   (where/error Store_out (invalidate-leases-in-store Store (read-address Ownership Address)))]
  )

(define-metafunction Dada
  write-place : Store place Value_new -> Store
  
  [(write-place Store (x f ...) Value_new)
   Store_out
   (where/error Value_0 (var-in-store Store x))
   (where/error (Value_1 Store_1) (write-fields Store Value_0 (f ...) Value_new))
   (where/error Store_out (store-with-updated-var Store_1 x Value_1))]
  )

(define-metafunction Dada
  write-fields : Store Unboxed-value_old (f ...) Value_new -> (Unboxed-value Store)
  
  [(write-fields Store _ () Value_new)
   (Value_new Store)]
  
  [(write-fields Store (Ownership box Address) (f_0 f_1 ...) Value_new)
   ((Ownership box Address) Store_3)
   (where/error Unboxed-value_0 (load-heap Store Address))
   (where/error (Unboxed-value_1 Store_1) (write-fields Store Unboxed-value_0 (f_0 f_1 ...) Value_new))
   (where/error Store_2 (store-heap Store_1 Address Unboxed-value_1))
   (where/error Store_3 (invalidate-leases-in-store Store_2 (write-address Ownership Address)))]

  [(write-fields Store (Aggregate-id (Field-value_0 ... (f_0 Value_f0_old) Field-value_1 ...)) (f_0 f_1 ...) Value_new)
   ((Aggregate-id (Field-value_0 ... (f_0 Value_f0_new) Field-value_1 ...)) Store_f0_new)
   (where/error (Value_f0_new Store_f0_new) (write-fields Store Value_f0_old (f_1 ...) Value_new))]
  
  )

(define-metafunction Dada
  write-action : Ownership Address -> Action
  
  [(write-action my Address) (write-address Address)]
  [(write-action (leased Lease) Address) (write-lease Lease)]
  )

(define-metafunction Dada
  share-place : Store place -> (Value Store)
  
  [(share-place Store place)
   (share-value Store_0 Leases_0 Value_0)
   (where/error (Value_0 Leases_0 Store_0) (read-place Store place))]
  )

(define-metafunction Dada
  share-value : Store Leases Value -> (Value Store)

  [(share-value Store Leases Value)
   (Value (clone-value Store Value))
   (where #t (is-data? Store Value))]
  
  [(share-value Store Leases (Ownership box Address))
   (((leased Lease) box Address) Store_out)
   (where/error (Lease Store_out) (create-lease-mapping Store shared Leases Address))]
  
  )

(define-metafunction Dada
  lend-place : Store place -> (Value Store)
  
  [; Lend out a class (the only thing we can lend out)
   (lend-place Store place)
   (((leased Lease) box Address) Store_out)
   (where/error (Value (Lease_read ...) Store_read) (read-place Store place))
   (where #f (is-data? Store_read Value))
   (where (Ownership box Address) Value)
   (where (Lease_own ...) (ownership-leases Ownership))
   (where (Lease Store_out) (create-lease-mapping Store_read borrowed (Lease_read ... Lease_own ...) Address))]
  
  )

(define-metafunction Dada
  is-data? : Store Unboxed-value -> boolean
  
  [(is-data? Store number) #t]
  
  [; Box: deref to see what's on the other side
   (is-data? Store (my box Address))
   (is-data? Store (load-heap Store Address))]

  [; Borrowed must be a class
   (is-data? Store ((leased Lease) box Address))
   #f
   (where borrowed (kind-of-lease Store Lease))]

  [; Shared class is data
   (is-data? Store ((leased Lease) box Address))
   #t
   (where shared (kind-of-lease Store Lease))]

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
     (term ([Stack-mappings]
            [(an-int (box 3 22))
             (another-int (box 1 44))
             (struct-1 (box 1 ((class some-struct) [(f0 (my box an-int)) (f1 (my box struct-2))])))
             (struct-2 (box 2 ((class another-struct) [(f0 66)])))
             (class-1 (box 1 ((class some-class) [(f0 88)])))]
            [])))
    ]
   
   (test-equal-terms (deref Store (var-in-store Store x0))
                     22)
   (test-equal-terms (var-in-store Store x1)
                     (my box struct-1))
   (test-equal-terms (deref Store (var-in-store Store x1))
                     ((class some-struct) [(f0 (my box an-int)) (f1 (my box struct-2))]))
   (test-equal-terms (read-place Store (x1 f0))
                     ((my box an-int) () Store))                   
   (test-match-terms Dada
                     (read-place (write-place Store (x1 f0) (my box another-int)) (x1 f0))
                     ((my box another-int) () Store))

   (test-equal-terms (read-place Store (x2 f0))
                     (66 () Store))
   (test-match-terms Dada
                     (read-place (write-place Store (x2 f0) 88) (x2 f0))
                     (88 () _))
   (test-match-terms Dada (share-place Store (x0)) ((my box an-int) [_ (_ ... (an-int (box 4 22)) _ ...) _]))
   (test-equal-terms (share-place Store (x2 f0)) (66 Store))
   (test-match-terms Dada
                     (share-place Store (x4))
                     (((leased Lease-id) box class-1) [_ _ [(Lease-id (shared () class-1))]]))
   )
  )
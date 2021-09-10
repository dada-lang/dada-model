#lang racket
(require redex
         "../grammar.rkt"
         "../util.rkt"
         "lang.rkt"
         "heap.rkt"
         "lease.rkt")
(provide drop-value
         drop-values)

(define-metafunction Dada
  ;; drop-value
  drop-value : Store Value -> Store
  
  [; Dropping a borrowed lease: no-op. Invalidates the lease.
   (drop-value Store ((leased Lease) box _))
   (invalidate-leases-in-store Store (drop-lease Lease))
   (where borrowed (kind-of-lease Store Lease))]
  [; Dropping a shared lease: no-op. There could be other copies
   ; with the same lease.
   (drop-value Store ((leased Lease) box _))
   Store
   (where shared (kind-of-lease Store Lease))]
  [; Dropping a number: no-op.
   (drop-value Store number) Store]
  [; Dropping expired data no-op.
   (drop-value Store expired) Store]
  [; Dropping data that you own will decrement its ref count,
   ; and possibly recursively drop the contents.
   (drop-value Store (my box Address))
   (decrement-ref-count Store Address)]
  )

(define-metafunction Dada
  ;; decrement-ref-count
  decrement-ref-count : Store Address -> Store
  
  [; Ref count is 1: remove from heap and drop value
   (decrement-ref-count Store Address)
   Store_3
   (where (Heap-mapping_0 ... (Address (box 1 Unboxed-value)) Heap-mapping_1 ...) (the-heap Store))
   (where/error Store_1 (store-with-heap Store (Heap-mapping_0 ... Heap-mapping_1 ...)))
   (where/error Store_2 (invalidate-leases-in-store Store_1 (drop-address Address)))
   (where/error Store_3 (drop-unboxed-value Store_2 Unboxed-value))
   ]

  [; Ref count is >1: decrement
   (decrement-ref-count Store Address)
   Store_1
   (where/error (Heap-mapping_0 ... (Address (box Ref-count Unboxed-value)) Heap-mapping_1 ...) (the-heap Store))
   (where/error Ref-count_1 ,(- (term Ref-count) 1))
   (where/error Store_1 (store-with-heap Store (Heap-mapping_0 ... (Address (box Ref-count_1 Unboxed-value)) Heap-mapping_1 ...)))
   ]
  )

(define-metafunction Dada
  ;; drop-unboxed-value

  drop-unboxed-value : Store Unboxed-value -> Store
  
  [(drop-unboxed-value Store (Aggregate-id [(f Value) ...]))
   (drop-values Store (Value ...))]
  
  [(drop-unboxed-value Store Value)
   (drop-value Store Value)]
  )

(define-metafunction Dada
  ;; drop-values
  drop-values : Store (Value ...) -> Store
  
  [(drop-values Store []) Store]

  [(drop-values Store [Value_0 Value_1 ...])
   (drop-values (drop-value Store Value_0) [Value_1 ...])]
 
  )

(module+ test
  (redex-let*
   Dada
   [(Store (term ([]
                  [(a (box 1 ((data tuple-2) [(f0 (my box b)) (f1 (my box c))])))
                   (b (box 3 22))
                   (c (box 1 ((data tuple-3) [(f0 (my box b)) (f1 ((leased Lease-id) box d)) (f2 66)])))
                   (d (box 1 44))]
                  [(Lease-id (borrowed () d))])))
    ]
   (test-equal-terms
    (the-heap (drop-value Store (my box a)))
    [(b (box 1 22)) ; ref count got dropped to 1
     (d (box 1 44))]) ; was shared, ref count didn't change
   )
  )
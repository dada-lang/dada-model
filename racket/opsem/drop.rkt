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

  [; Dropping a lent lease: no-op. Invalidates the lease.
   ;
   ; FIXME: I think this is actually the wrong behavior. Consider
   ; something like `fn(&mut self) -> &mut T` in Rust!
   (drop-value Store ((lent Lease) box _))
   (invalidate-leases-in-store Store (drop-lease Lease))
   ]
  [; Dropping a shared lease: no-op. There could be other copies
   ; with the same lease.
   (drop-value Store ((shared Lease) box _))
   Store
   ]
  [; Dropping expired data no-op.
   (drop-value Store expired) Store]
  [; Dropping data that you own will decrement its ref count,
   ; and possibly recursively drop the contents.
   (drop-value Store (Owned-kind box Address))
   (decrement-ref-count-for Store Address)]
  )

(define-metafunction Dada
  ;; decrement-ref-count
  decrement-ref-count-for : Store Address -> Store

  [; Ref count is 1: remove from heap and drop value
   (decrement-ref-count-for Store Address)
   Store_3
   (where (Heap-mapping_0 ... (Address (box 1 Unboxed-value)) Heap-mapping_1 ...) (the-heap Store))
   (where/error Store_1 (store-with-heap Store (Heap-mapping_0 ... Heap-mapping_1 ...)))
   (where/error Store_2 (invalidate-leases-in-store Store_1 (drop-address Address)))
   (where/error Store_3 (drop-unboxed-value Store_2 Unboxed-value))
   ]

  [; Ref count is >1: decrement
   (decrement-ref-count-for Store Address)
   Store_1
   (where/error (Heap-mapping_0 ... (Address (box Ref-count Unboxed-value)) Heap-mapping_1 ...) (the-heap Store))
   (where/error Ref-count_1 (decrement-ref-count Ref-count))
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

  [; Dropping a number: no-op.
   (drop-unboxed-value Store number) Store]
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
                  [(a (box 1 ((class tuple-2) [(f0 (my box b)) (f1 (my box c))])))
                   (b (box 3 22))
                   (c (box 1 ((class tuple-3) [(f0 (my box b)) (f1 ((lent Lease-id) box d)) (f2 (our box e))])))
                   (d (box 1 44))
                   (e (box 1 66))]
                  [(Lease-id (lent () d))])))
    ]
   (test-equal-terms
    (the-heap (drop-value Store (my box a)))
    [(b (box 1 22)) ; ref count got dropped to 1
     (d (box 1 44))]) ; was shared, ref count didn't change
   )
  )
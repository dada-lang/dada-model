#lang racket
(require redex
         "../util.rkt"
         "lang.rkt"
         "heap.rkt")
(provide clone-value)

(define-metafunction Dada
  ;; clone-value
  ;;
  ;; Given a value that is to be cloned, return the new value
  ;; that should be stored both in the old and new places. This
  ;; may require adjusting ref-counts.
  ;;
  ;; Cloning a uniquely owned value is not possible.
  clone-value : Store Value -> Store

  [(clone-value Store ((shared _) box Address)) Store]

  [(clone-value Store number) Store]

  [(clone-value Store (our box Address))
   (store-with-heap Store (Heap-mapping_0 ... (Address (box Ref-count_1 Unboxed-value)) Heap-mapping_1 ...))
   (where/error (Heap-mapping_0 ... (Address (box Ref-count Unboxed-value)) Heap-mapping_1 ...) (the-heap Store))
   (where/error Ref-count_1 (increment-ref-count Ref-count))]
  )

(module+ test
  (redex-let*
   Dada
   [(((my box Address) Store_a) (term (allocate-box-in-store Store_empty 22)))
    (Store_b (term (clone-value Store_a (our box Address))))
    (Store_c (term (clone-value Store_b (our box Address))))
    (Store_d (term (clone-value Store_c ((shared Lease-id) box Address))))
    (Store_z (term (clone-value Store_empty (our box Zero))))
    ]

   (test-equal-terms (load-ref-count Store_a Address) 1)
   (test-equal-terms (load-ref-count Store_b Address) 2)
   (test-equal-terms (load-ref-count Store_c Address) 3)
   (test-equal-terms (load-ref-count Store_d Address) 3)
   (test-equal-terms (load-ref-count Store_z Zero) static)
   ))

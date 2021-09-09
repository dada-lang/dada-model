#lang racket
(require redex
         "../grammar.rkt"
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
  clone-value : Store Value -> Store

  [(clone-value Store ((leased _) box Address)) Store]

  [(clone-value Store number) Store]
  
  [(clone-value Store (my box Address))
   (store-with-heap Store (Heap-mapping_0 ... (Address (box Ref-count_1 Unboxed-value)) Heap-mapping_1 ...))
   (where/error (Heap-mapping_0 ... (Address (box Ref-count Unboxed-value)) Heap-mapping_1 ...) (the-heap Store))
   (where/error Ref-count_1 ,(+ 1 (term Ref-count)))]
  )

(module+ test
  (redex-let*
   Dada
   [(((my box Address) Store_a) (term (allocate-box-in-store Store_empty 22)))
    (Store_b (term (clone-value Store_a (my box Address))))
    (Store_c (term (clone-value Store_b (my box Address))))
    (Store_d (term (clone-value Store_c ((leased Lease-id) box Address))))
    ]

   (test-equal-terms (load-ref-count Store_a Address) 1)
   (test-equal-terms (load-ref-count Store_b Address) 2)
   (test-equal-terms (load-ref-count Store_c Address) 3)
   (test-equal-terms (load-ref-count Store_d Address) 3)
   ))

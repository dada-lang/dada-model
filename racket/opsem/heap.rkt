#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         "../grammar.rkt"
         "../type-system.rkt"
         "../util.rkt"
         "lang.rkt")
(provide (all-defined-out))

(define-metafunction Dada
  ;; fresh-address
  ;;
  ;; Return a fresh address that is specific to the ref counts table.
  
  fresh-address : Heap-mappings  -> Address
  [(fresh-address Heap-mappings) ,(variable-not-in (term Heap-mappings) 'Heap-addr)]
  )

(define-metafunction Dada
  ;; allocate-box-in-store
  ;;
  ;; Allocates a fresh box storing Unboxed-value and returns it.
  allocate-box-in-store : Store Unboxed-value -> (Value Store)
  
  [(allocate-box-in-store Store_0 Unboxed-value)
   ((my box Address) Store_1)
   (where/error Heap-mappings_0 (the-heap Store_0))
   (where/error (Address Heap-mappings_1) (allocate-heap-value Heap-mappings_0 Unboxed-value))
   (where/error Store_1 (store-with-heap Store_0 Heap-mappings_1))]
  )


(define-metafunction Dada
  ;; allocate-heap-value
  ;;
  ;; Allocates a fresh ref count that initially has the value given.
  allocate-heap-value : Heap-mappings Unboxed-value -> (Address Heap-mappings)
  
  [(allocate-heap-value (Heap-mapping ...) Unboxed-value)
   (Address (Heap-mapping ... (Address (box 1 Unboxed-value))))
   (where Address (fresh-address (Heap-mapping ...)))]
  
  )

(module+ test
  (test-equal-terms (allocate-heap-value [] 22)
                    (Heap-addr ((Heap-addr (box 1 22)))))
  (test-equal-terms (allocate-box-in-store Store_empty 22)
                    ((my box Heap-addr) ([] ((Heap-addr (box 1 22))))))
  )

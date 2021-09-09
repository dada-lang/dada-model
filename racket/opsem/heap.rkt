#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         "../grammar.rkt"
         "../type-system.rkt"
         "../util.rkt"
         "lang.rkt")
(provide the-heap
         store-with-heap
         store-with-heap-entry
         store-with-heap-entries
         load-heap
         load-ref-count
         store-heap
         allocate-box-in-store)

(define-metafunction Dada
  the-heap : Store -> Heap-mappings
  [(the-heap (_ Heap-mappings _)) Heap-mappings])

(define-metafunction Dada
  store-with-heap : Store Heap-mappings -> Store
  [(store-with-heap (Stack-segments _ Lease-mappings) Heap-mappings) (Stack-segments Heap-mappings Lease-mappings)])

(define-metafunction Dada
  ;; store-with-heap-entry
  ;;
  ;; Returns a new store that contains Heap-mapping (overwrites any old Heap-mapping
  ;; with the same address).
  store-with-heap-entry : Store Heap-mapping -> Store

  [(store-with-heap-entry Store (Address Boxed-value))
   (store-with-heap Store (Heap-mapping_0 ... (Address Boxed-value) Heap-mapping_1 ...))
   (where (Heap-mapping_0 ... (Address _) Heap-mapping_1 ...) (the-heap Store))]

  [(store-with-heap-entry Store Heap-mapping_0)
   (store-with-heap Store (Heap-mapping_0 Heap-mapping_1 ...))
   (where (Heap-mapping_1 ...) (the-heap Store))]
  )

(define-metafunction Dada
  ;; store-with-heap-entries
  store-with-heap-entries : Store Heap-mapping ... -> Store

  [(store-with-heap-entries Store) Store]

  [(store-with-heap-entries Store Heap-mapping_0 Heap-mapping_1 ...)
   (store-with-heap-entries (store-with-heap-entry Store Heap-mapping_0) Heap-mapping_1 ...)]
  
  )

(define-metafunction Dada
  ;; load-heap
  ;;
  ;; Load the Unboxed-value for the box at a given Address.
  load-heap : Store Address -> Unboxed-value
  [(load-heap Store Address)
   Unboxed-value
   (where (_ ... (Address (box _ Unboxed-value)) _ ...) (the-heap Store))]
  )

(define-metafunction Dada
  ;; load-ref-count
  ;;
  ;; Load the ref-count for the box at a given Address.
  load-ref-count : Store Address -> Ref-count

  [(load-ref-count Store Address)
   Ref-count
   (where (_ ... (Address (box Ref-count _)) _ ...) (the-heap Store))]
  )

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

(define-metafunction Dada
  ;; store-heap
  ;;
  ;; Update the value stored at Address, without changing its ref-count.
  store-heap : Store Address Unboxed-value -> Store
  [(store-heap Store Address Unboxed-value)
   (store-with-heap-entry Store (Address (box Ref-count Unboxed-value)))
   (where/error Ref-count (load-ref-count Store Address))]
  )

(module+ test
  (test-equal-terms (allocate-heap-value [] 22)
                    (Heap-addr ((Heap-addr (box 1 22)))))
  (test-equal-terms (allocate-box-in-store Store_empty 22)
                    ((my box Heap-addr) ([[]] ((Heap-addr (box 1 22))) [])))
  )

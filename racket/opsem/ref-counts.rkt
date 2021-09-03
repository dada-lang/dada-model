#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         "../grammar.rkt"
         "../type-system.rkt"
         "../util.rkt"
         "lang.rkt")
(provide (all-defined-out))

(define-metafunction Dada
  load-ref-count : Ref-mappings Address -> number
  [(load-ref-count (_ ... (Address number) _ ...) Address)
   number]
  )

(define-metafunction Dada
  ;; fresh-ref-count
  ;;
  ;; Return a fresh address that is specific to the ref counts table.
  
  fresh-ref-count : Ref-mappings  -> Address
  [(fresh-ref-count Ref-mappings) ,(variable-not-in (term Ref-mappings) 'Ref-mapping)]
  )

(define-metafunction Dada
  ;; allocate-ref-count
  ;;
  ;; Allocates a fresh ref count that initially has the value given.
  allocate-ref-count : Ref-mappings number -> (Address Ref-mappings)
  
  [(allocate-ref-count (Ref-mapping ...) number)
   (Address (Ref-mapping ... (Address number)))
   (where Address (fresh-ref-count (Ref-mapping ...)))]
  
  )

(define-metafunction Dada
  ;; increment-ref-count
  ;;
  ;; 
  increment-ref-count : Ref-mappings Address -> Ref-mappings
  [(increment-ref-count (Ref-mapping_0 ... (Address number) Ref-mapping_1 ...) Address)
   (Ref-mapping_0 ... (Address (increment number)) Ref-mapping_1 ...)]
  )

(define-metafunction Dada
  ;; decrement-ref-count
  ;;
  ;; Decrement the ref-count associated with Address and return (a) a new Ref-mappings list
  ;; and (b) true if the new ref-count is zero.
  decrement-ref-count : Ref-mappings Address -> (Ref-mappings boolean)
  
  [; If new ref count is zero, remove Address from the table.
   (decrement-ref-count (Ref-mapping_0 ... (Address number) Ref-mapping_1 ...) Address)
   ((Ref-mapping_0 ... Ref-mapping_1 ...) #t)
   (where 0 (decrement number))]

  [(decrement-ref-count (Ref-mapping_0 ... (Address number) Ref-mapping_1 ...) Address)
   ((Ref-mapping_0 ... (Address number_1) Ref-mapping_1 ...) #f)
   (where number_1 (decrement number))]
  )

(define-metafunction Dada
  increment : number -> number
  [(increment number) ,(+ (term number) 1)])

(define-metafunction Dada
  decrement : number -> number
  [(decrement number) ,(- (term number) 1)])

(module+ test
  (redex-let*
   Dada
   [(Ref-mappings (term [(i0 66) (i1 1) (i2 2)]))]

   (test-equal (term (load-ref-count Ref-mappings i0)) 66)
   (test-equal (term (load-ref-count (increment-ref-count Ref-mappings i0) i0)) 67)
   (test-match Dada ([(i0 66) (i2 2)] #t) (term (decrement-ref-count Ref-mappings i1)))
   (test-match Dada (_ #f) (term (decrement-ref-count Ref-mappings i2)))
   (test-equal-terms (allocate-ref-count Ref-mappings 22) (Ref-mapping ((i0 66) (i1 1) (i2 2) (Ref-mapping 22))))
   )
  )
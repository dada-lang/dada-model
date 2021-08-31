#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         "../grammar.rkt"
         "../type-system.rkt"
         "../util.rkt"
         "lang.rkt")
(provide (all-defined-out))

(define-metafunction Dada
  load-ref-count : Ref-counts Address -> number
  [(load-ref-count (_ ... (Address number) _ ...) Address)
   number]
  )

(define-metafunction Dada
  ;; fresh-ref-count
  ;;
  ;; Return a fresh address that is specific to the ref counts table.
  
  fresh-ref-count : Ref-counts  -> Address
  [(fresh-ref-count Ref-counts) ,(variable-not-in (term Ref-counts) 'Ref-count)]
  )

(define-metafunction Dada
  ;; allocate-ref-count
  ;;
  ;; Allocates a fresh ref count that initially has the value given.
  allocate-ref-count : Ref-counts number -> (Address Ref-counts)
  
  [(allocate-ref-count (Ref-count ...) number)
   (Address (Ref-count ... (Address number)))
   (where Address (fresh-ref-count (Ref-count ...)))]
  
  )

(define-metafunction Dada
  ;; increment-ref-count
  ;;
  ;; 
  increment-ref-count : Ref-counts Address -> Ref-counts
  [(increment-ref-count (Ref-count_0 ... (Address number) Ref-count_1 ...) Address)
   (Ref-count_0 ... (Address (increment number)) Ref-count_1 ...)]
  )

(define-metafunction Dada
  ;; decrement-ref-count
  ;;
  ;; Decrement the ref-count associated with Address and return (a) a new Ref-counts list
  ;; and (b) true if the new ref-count is zero.
  decrement-ref-count : Ref-counts Address -> (Ref-counts boolean)
  
  [; If new ref count is zero, remove Address from the table.
   (decrement-ref-count (Ref-count_0 ... (Address number) Ref-count_1 ...) Address)
   ((Ref-count_0 ... Ref-count_1 ...) #t)
   (where 0 (decrement number))]

  [(decrement-ref-count (Ref-count_0 ... (Address number) Ref-count_1 ...) Address)
   ((Ref-count_0 ... (Address number_1) Ref-count_1 ...) #f)
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
   [(Ref-counts (term [(i0 66) (i1 1) (i2 2)]))]

   (test-equal (term (load-ref-count Ref-counts i0)) 66)
   (test-equal (term (load-ref-count (increment-ref-count Ref-counts i0) i0)) 67)
   (test-match Dada ([(i0 66) (i2 2)] #t) (term (decrement-ref-count Ref-counts i1)))
   (test-match Dada (_ #f) (term (decrement-ref-count Ref-counts i2)))
   (test-equal-terms (allocate-ref-count Ref-counts 22) (Ref-count ((i0 66) (i1 1) (i2 2) (Ref-count 22))))
   )
  )
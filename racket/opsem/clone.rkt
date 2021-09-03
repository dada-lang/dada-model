#lang racket
(require redex
         "../grammar.rkt"
         "../util.rkt"
         "lang.rkt"
         "ref-counts.rkt")
(provide clone-value)

(define-metafunction Dada
  ;; clone-value
  ;;
  ;; Given a value that is to be cloned, return the new value
  ;; that should be stored both in the old and new places. This
  ;; may require adjusting ref-counts.
  clone-value : Ref-mappings Value -> Ref-mappings
  [(clone-value Ref-mappings number) Ref-mappings]
  [(clone-value Ref-mappings (Identity id Field-values))
   Ref-mappings_1
   (where Ref-mappings_1 (clone-identity Ref-mappings Identity))]
  [(clone-value Ref-mappings (Identity box Address))
   Ref-mappings_1
   (where Ref-mappings_1 (clone-identity Ref-mappings Identity))]
  )

(define-metafunction Dada
  ;; clone-identity
  ;;
  ;; Given a value that is to be cloned, return the new value
  ;; that should be stored both in the old and new places. This
  ;; may require adjusting ref-counts.
  clone-identity : Ref-mappings Identity -> Ref-mappings
  [(clone-identity Ref-mappings shared)
   Ref-mappings]
  
  [(clone-identity Ref-mappings (my Address))
   Ref-mappings_1
   (where Ref-mappings_1 (increment-ref-count Ref-mappings Address))]
  
  [(clone-identity Ref-mappings data)
   Ref-mappings]
  )

(module+ test
  (redex-let*
   Dada
   [(Ref-mappings (term [(i0 1)]))]

   (test-equal-terms (clone-identity Ref-mappings (my i0)) ((i0 2)))
   (test-equal-terms (clone-identity Ref-mappings shared) Ref-mappings)
   )
  )

(module+ test
   (test-equal-terms (clone-value [(i0 1)] ((my i0) box dummy-address)) ((i0 2)))
   (test-equal-terms (clone-value [(i0 1)] ((my i0) dummy-struct-name ())) ((i0 2)))   

  (test-equal-terms (clone-value [(i0 1) (i1 1)] ((my i0) dummy-data-name ((f0 ((my i1) dummy-struct-name ()))))) ((i0 2) (i1 1)))
  )
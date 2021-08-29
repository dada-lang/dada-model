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
  clone-value : Ref-counts Value -> (Ref-counts Value)
  [(clone-value Ref-counts number) (Ref-counts number)]
  [(clone-value Ref-counts (Identity id Field-values))
   (Ref-counts_1 (Identity_1 id Field-values))
   (where (Ref-counts_1 Identity_1) (clone-identity Ref-counts Identity))]
  [(clone-value Ref-counts (box Identity Address))
   (Ref-counts_1 (box Identity_1 Address))
   (where (Ref-counts_1 Identity_1) (clone-identity Ref-counts Identity))]
  )

(define-metafunction Dada
  ;; clone-identity
  ;;
  ;; Given a value that is to be cloned, return the new value
  ;; that should be stored both in the old and new places. This
  ;; may require adjusting ref-counts.
  clone-identity : Ref-counts Identity -> (Ref-counts Identity)
  [(clone-identity Ref-counts shared)
   (Ref-counts shared)]
  [(clone-identity Ref-counts (my Address))
   (Ref-counts_1 (my Address))
   (where Ref-counts_1 (increment-ref-count Ref-counts Address))]
  [(clone-identity Ref-counts data)
   (Ref-counts data)]
  )

(module+ test
  (redex-let*
   Dada
   [(Ref-counts (term [(i0 1)]))]

   (test-equal-terms (clone-identity Ref-counts (my i0)) (((i0 2)) (my i0)))
   (test-equal-terms (clone-identity Ref-counts shared) (Ref-counts shared))
   )
  )

(module+ test
  (redex-let*
   Dada
   [(Ref-counts (term [(i0 1)]))]

   (test-equal-terms (clone-value Ref-counts (box (my i0) dummy)) (((i0 2)) (box (my i0) dummy)))
   )
  )
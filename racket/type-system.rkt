#lang racket
(require redex)
(require "grammar.rkt")
(provide (all-defined-out))

(define-extended-language dada-type-system dada
  ;; an "access mode" indicates what happens to a value `v` of type `ty`
  ;; after it has been accessed with the mode `my`:
  ;;
  ;; * move -- the old value is invalidated. This occurs if `v` has any
  ;;   uniquely owned things (e.g., `my C`).
  ;; * reborrow -- borrowed things are 'reborrowed' for the next value,
  ;;   which means that the old value cannot be used until the new value
  ;;   is finished. Note that this may also require increasing ref counts
  ;;   for `our` values found within.
  ;; * clone -- increase ref counts for `our` values
  ;; * copy -- no action needed
  (access-mode move reborrow clone copy)
  )

;; combine-access-mode: takes the most demanding access mode
(define-metafunction dada-type-system
  combine-access-mode : access-mode access-mode -> access-mode
  [(combine-access-mode access-mode_1 access-mode_2)
   ,(match
        (term (access-mode_1 access-mode_2))
      [(list 'move _) 'move]
      [(list _ 'move) 'move]
      [(list 'reborrow _) 'reborrow]
      [(list _ 'reborrow) 'reborrow]
      [(list 'clone _) 'clone]
      [(list _ 'clone) 'clone]
      [(list 'copy 'copy) 'copy])])

(test-equal (term (combine-access-mode move reborrow)) (term move))
(test-equal (term (combine-access-mode reborrow move)) (term move))
(test-equal (term (combine-access-mode clone move)) (term move))
(test-equal (term (combine-access-mode clone copy)) (term clone))
(test-equal (term (combine-access-mode copy clone)) (term clone))

;; combine-access-modes: given a list of modes, finds the max
(define-metafunction dada-type-system
  combine-access-modes : (access-mode ...) -> access-mode
  [(combine-access-modes ()) copy]
  [(combine-access-modes (access-mode_0 access-mode_1 ...)) (combine-access-mode access-mode_0 (combine-access-modes (access-mode_1 ...)))])


(test-equal (term (combine-access-modes (copy copy clone copy))) (term clone))
(test-equal (term (combine-access-modes (move copy reborrow clone))) (term move))
(test-equal (term (combine-access-modes (copy clone clone move))) (term move))
(test-equal (term (combine-access-modes (copy clone clone reborrow))) (term reborrow))

;; `(ty-access-mode program ty)`: After a value of type `ty` is
;; "moved" with `my`, what operation is needed? This is determined
;; by walking the type recursively to determine what sort of classes
;; are found within.
;;
;; - `move` -- remove the old value
;; - `borrow` -- reborrow existing 
;; - `clone` -- increase ref-counts on `our` classes
;; - `copy` -- just clone (only shared classes or structs)
(define-metafunction dada-type-system
  ty-access-mode : program ty -> access-mode
  [(ty-access-mode program (my c)) move]
  [(ty-access-mode program (our c)) clone]
  [(ty-access-mode program ((borrowed _) c)) reborrow]
  [(ty-access-mode program ((shared _) c)) copy]
  [(ty-access-mode program int) copy]
  [(ty-access-mode program s) (struct-access-mode program s (struct-named program s))]
  )

(define-metafunction dada-type-system
  struct-access-mode : program s struct-definition -> access-mode
  [(struct-access-mode program s (struct ((f ty) ...)))
   (combine-access-modes ((ty-access-mode program ty) ...))])

(let [(program
       (term (; classes:
              [
               (some-class (class []))
              ]
              ; structs:
              [
               (copy-struct (struct [(f0 int) (f1 int)]))
               (shared-struct (struct [(f0 ((shared ()) some-class)) (f1 int)]))
               (clone-struct (struct [(f0 int) (f1 (our some-class))]))
               (borrowed-struct (struct [(f0 ((borrowed ()) some-class)) (f1 (our some-class))]))
               (move-struct (struct [(f0 (my some-class)) (f1 (our some-class))]))
              ]
              ; methods:
              []
              )))]
  (test-equal (term (ty-access-mode ,program copy-struct)) (term copy))
  (test-equal (term (ty-access-mode ,program shared-struct)) (term copy))
  (test-equal (term (ty-access-mode ,program clone-struct)) (term clone))
  (test-equal (term (ty-access-mode ,program borrowed-struct)) (term reborrow))
  (test-equal (term (ty-access-mode ,program move-struct)) (term move))
  )

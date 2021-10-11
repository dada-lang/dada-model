#lang racket
(require redex/reduction-semantics
         "racket/dada.rkt"
         "racket/util.rkt"
         "racket/opsem/traverse.rkt")

(current-traced-metafunctions '(write-traversal-origin swap-traversal read-traversal read-traversal-origin))

(; Test writing to an integer stored in an atomic field
 dada-let-store
 ; Heap-addr = 22
 ; Heap-addr1 = Cell
 ((Store = [(var cell = (class-instance Cell (int) (22)))])
  (Traversal_0 (term (traversal program_test Store (cell value)))))
 (test-equal-terms (swap-traversal Store Traversal_0 (my box test))
                   (((read-address my Heap-addr1)
                     (update-address
                      Heap-addr1
                      ((class Cell) (value (my box test)))))))
 )
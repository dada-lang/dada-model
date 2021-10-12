#lang racket

(require redex/reduction-semantics
         "../dada.rkt"
         "../opsem/traverse.rkt"
         "../opsem/action.rkt"
         "../util.rkt")

(; Test writing to the field `x` of a Point stored in an atomic field
 dada-let-store
 ((Store = [(var cell = (class-instance Cell ((my Point ())) ((class-instance Point () (22 44)))))
            (var p = (lend (cell value)))
            ]
         ; Heap-addr = 22
         ; Heap-addr1 = 44
         ; Heap-addr2 = Point
         ; Heap-addr3 = Cell
         )
  (Traversal_0 (term (traversal program_test Store (cell value))))
  ((Actions_swap _) (term (swap-traversal Store Traversal_0 (my box test))))
  (; Subtle: the *swap traversal* doesn't invalidate `p`. The point was swapped
   ; out but it remains lent and unaffected by that. The type system might or might not
   ; accept this.
   Store_expected (term (test-store ((cell (my box Heap-addr3))
                                     (p ((lent Lease-id) box Heap-addr2)))
                                    ((Heap-addr (box 1 22))
                                     (Heap-addr1 (box 1 44))
                                     (Heap-addr2
                                      (box
                                       1
                                       ((class Point)
                                        ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
                                     (Heap-addr3
                                      (box 1 ((class Cell) ((value (my box test)))))))
                                    ((Lease-id (lent () Heap-addr2))))))
  )
 #;(pretty-print (term Store))
 #;(pretty-print (term Actions_swap))
 #;(current-traced-metafunctions '(apply-action-to-value lease-valid))
 (test-equal-terms (apply-actions-to-store Store Actions_swap)
                   Store_expected)
 )

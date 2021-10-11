#lang racket

(require redex/reduction-semantics
         "../dada.rkt"
         "../opsem/traverse.rkt"
         "../util.rkt")

(dada-let-store
 ((Store = [(var p = (class-instance Point () (22 44)))])
  (Traversal_0 (term (traversal program_test Store (p x)))))
 (test-equal-terms (read-traversal Store Traversal_0)
                   (((read-address my Heap-addr2)) (our box Heap-addr)))
 )

(dada-let-store
 ((Store = [(var p = (class-instance Shared
                                     ((my Point ()))
                                     ((class-instance Point () (22 44)))))])
  (Traversal_0 (term (traversal program_test Store (p a x)))))
 (test-equal-terms (swap-traversal Store Traversal_0 (my box test))
                   ((expired
                     (update-address
                      my
                      Heap-addr2
                      ((class Point)
                       ((x (my box test)) (y (our box Heap-addr1))))))
                    (our box Heap-addr)))
 )


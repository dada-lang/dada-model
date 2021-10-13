#lang racket

(require redex/reduction-semantics
         "../dada.rkt"
         "../opsem/traverse.rkt"
         "../util.rkt")

(; Test reading a field of an owned point
 dada-let-store
 ((Store = [(var p = (class-instance Point () (22 44)))]
         ; Heap-addr = 22
         ; Heap-addr1 = 44
         ; Heap-addr2 = Point
         )
  (Traversal_0 (term (traversal program_test Store (p x)))))
 (test-equal-terms (read-traversal Store Traversal_0)
                   (((read-address my Heap-addr2)) (our box Heap-addr)))
 )

(; Attempt to mutate a frozen value
 dada-let-store
 ((Store = [(var p = (freeze (class-instance Point () (22 44))))]
         ; Heap-addr = 22
         ; Heap-addr1 = 44
         ; Heap-addr2 = Point
         )
  (Traversal_0 (term (traversal program_test Store (p x)))))
 (test-equal-terms (swap-traversal Store Traversal_0 (my box test))
                   ((expired
                     (update-address
                      Heap-addr2
                      ((class Point)
                       ((x (my box test)) (y (our box Heap-addr1))))))
                    (our box Heap-addr)))
 )

(; Attempt to write through a shared field
 dada-let-store
 ((Store = [(var p = (class-instance Shared
                                     ((my Point ()))
                                     ((class-instance Point () (22 44)))))]
         ; Heap-addr = 22
         ; Heap-addr1 = 44
         ; Heap-addr2 = Point
         ; Heap-addr3 = Shared
         )
  (Traversal_0 (term (traversal program_test Store (p a x)))))
 (test-equal-terms (swap-traversal Store Traversal_0 (my box test))
                   ((expired
                     (write-address my Heap-addr2)
                     (update-address
                      Heap-addr2
                      ((class Point)
                       ((x (my box test)) (y (our box Heap-addr1))))))
                    (our box Heap-addr)))
 )

(; Test writing to the field `x` of a Point stored in an atomic field
 dada-let-store
 ((Store = [(var cell = (class-instance Cell ((my Point ())) ((class-instance Point () (22 44)))))]
         ; Heap-addr = 22
         ; Heap-addr1 = 44
         ; Heap-addr2 = Point
         ; Heap-addr3 = Cell
         )
  (Traversal_0 (term (traversal program_test Store (cell value x)))))
 (test-equal-terms (swap-traversal Store Traversal_0 (my box test))
                   (((read-address my Heap-addr3)
                     (write-address my Heap-addr2)
                     (update-address
                      Heap-addr2
                      ((class Point)
                       ((x (my box test)) (y (our box Heap-addr1))))))
                    (our box Heap-addr)))
 )

(; Test writing to an integer stored in an atomic field
 dada-let-store
 ((Store = [(var cell = (class-instance Cell (int) (22)))]
         ; Heap-addr = 22
         ; Heap-addr1 = Cell
         )
  (Traversal_0 (term (traversal program_test Store (cell value)))))
 (test-equal-terms (swap-traversal Store Traversal_0 (my box test))
                   (((read-address my Heap-addr1)
                     (update-address
                      Heap-addr1
                      ((class Cell) ((value (my box test))))))
                    (our box Heap-addr)))
 )




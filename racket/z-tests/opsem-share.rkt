#lang racket

(require redex
         "../dada.rkt")

(; NB: Reading `point x` expires both `lent-point` and `shared-point2`
 dada-seq-test [(var point = (class-instance Point () (22 44)))
                (var lent-point = (lend (point)))
                (var some = (class-instance Some
                                            (((lent ((lent (point)))) Point ()))
                                            ((give (lent-point)))))
                (var shared-some = (share (some)))
                (var shared-point2 = (share (shared-some value)))
                (copy (point x))
                ]
               [(point (my box Heap-addr2))
                (lent-point expired)
                (some (my box Heap-addr3))
                (shared-some ((shared Lease-id1) box Heap-addr3))
                (shared-point2 expired)
                ]
               [(Heap-addr (box 2 22))
                (Heap-addr1 (box 1 44))
                (Heap-addr2 (box 1 ((class Point) ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
                (Heap-addr3 (box 1 ((class Some) ((value expired)))))
                ]
               [(Lease-id1 (shared () Heap-addr3))
                ]
               (our box Heap-addr))
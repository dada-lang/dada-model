#lang racket

(require redex
         "../dada.rkt")

(; FIXME-- the result of doing this read *ought* to invalidate `shared-point2`
 dada-seq-test [(var point = (class-instance Point () (22 44)))
                (var lent-point = (lend (point)))
                (var some = (class-instance Some
                                            (((lent ((lent (point)))) Point ()))
                                            ((give (lent-point)))))
                (var shared-some = (share (some)))
                (var shared-point2 = (share (shared-some value)))
                (copy (point x))
                ]
               [(point (my box Heap-addr))
                (lent-point expired)
                (some (my box Heap-addr1))
                (shared-some ((leased Lease-id1) box Heap-addr1))
                (shared-point2 ((leased Lease-id2) box Heap-addr))
                ]
               [(Heap-addr1 (box 1 ((class Some) ((value expired)))))
                (Heap-addr (box 1 ((class Point) ((x 22) (y 44)))))
                ]
               [(Lease-id1 (shared () Heap-addr1))
                (Lease-id2 (shared (Lease-id1) Heap-addr))
                ]
               22)
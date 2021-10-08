#lang racket

(require redex
         "../dada.rkt")

(; Moving something that is uniquely owned moves.
 dada-seq-test
 ((var p = (class-instance Point () (22 44)))
  (var q = (move (p)))
  )
 [(p expired)
  (q (my box Heap-addr))]
 [(Heap-addr (box 1 ((class Point) ((x 22) (y 44)))))]
 []
 0)

(; Moving something that is lent creates a sublease.
 dada-seq-test
 ((var p = (class-instance Point () (22 44)))
  (var q = (lend (p)))
  (var r = (move (q)))
  )
 [(p (my box Heap-addr))
  (q ((lent Lease-id) box Heap-addr))
  (r ((lent Lease-id1) box Heap-addr))]
 [(Heap-addr (box 1 ((class Point) ((x 22) (y 44)))))]
 [(Lease-id (lent () Heap-addr))
  (Lease-id1 (lent (Lease-id) Heap-addr))]
 0)

(; Moving something that is shared clones the lease.
 dada-seq-test
 ((var p = (class-instance Point () (22 44)))
  (var q = (share (p)))
  (var r = (move (q)))
  )
 [(p (my box Heap-addr))
  (q ((shared Lease-id) box Heap-addr))
  (r ((shared Lease-id) box Heap-addr))]
 [(Heap-addr (box 1 ((class Point) ((x 22) (y 44)))))]
 [(Lease-id (shared () Heap-addr))]
 0)

(; Moving a (my String) value contained within a
 ; p: (lent Some<my Point>) gives a (lent String),
 ; subleased from `p`.
 dada-seq-test
 ((var some-point = (class-instance Some ((my Point ())) ((class-instance Point () (22 44)))))
  (var p = (lend (some-point)))
  (var r = (move (p value)))
  )
 [(some-point (my box Heap-addr1))
  (p ((lent Lease-id) box Heap-addr1))
  (r ((lent Lease-id1) box Heap-addr))]
 [(Heap-addr1 (box 1 ((class Some) ((value (my box Heap-addr))))))
  (Heap-addr (box 1 ((class Point) ((x 22) (y 44)))))
  ]
 [(Lease-id (lent () Heap-addr1))
  (Lease-id1 (lent (Lease-id) Heap-addr))]
 0)

(; Moving a (shared String) value contained within a
 ; p: (lent Some<my Point>) clones the shared string.
 dada-seq-test
 ((var point = (class-instance Point () (22 44)))
  (var shared-point = (share (point)))
  (var some-shared-point = (class-instance Some (((shared ((shared (point)))) Point ())) ((copy (shared-point)))))
  (var p = (lend (some-shared-point)))
  (var r = (move (p value)))
  )
 [(point (my box Heap-addr))
  (shared-point ((shared Lease-id) box Heap-addr))
  (some-shared-point (my box Heap-addr1))
  (p ((lent Lease-id1) box Heap-addr1))
  (r ((shared Lease-id) box Heap-addr))]
 [(Heap-addr1 (box 1 ((class Some) ((value ((shared Lease-id) box Heap-addr))))))
  (Heap-addr (box 1 ((class Point) ((x 22) (y 44)))))
  ]
 [(Lease-id (shared () Heap-addr))
  (Lease-id1 (lent () Heap-addr1))]
 0)

(; Moving a (lent String) value contained within a
 ; p: (lent Some<my Point>) subleases the two lent variables.
 dada-seq-test
 ((var point = (class-instance Point () (22 44)))
  (var lent-point = (lend (point)))
  (var some-lent-point = (class-instance Some (((lent ((lent (point)))) Point ())) ((give (lent-point)))))
  (var p = (lend (some-lent-point)))
  (var r = (move (p value)))
  )
 [(point (my box Heap-addr))
  (lent-point expired)
  (some-lent-point (my box Heap-addr1))
  (p ((lent Lease-id1) box Heap-addr1))
  (r ((lent Lease-id2) box Heap-addr))]
 [(Heap-addr1 (box 1 ((class Some) ((value ((lent Lease-id) box Heap-addr))))))
  (Heap-addr (box 1 ((class Point) ((x 22) (y 44)))))
  ]
 [(Lease-id (lent () Heap-addr))
  (Lease-id1 (lent () Heap-addr1))
  (Lease-id2 (lent (Lease-id1 Lease-id) Heap-addr))]
 0)
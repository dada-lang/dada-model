#lang racket

(require "../dada.rkt")

(; Moving something that is uniquely owned moves.
 dada-seq-test
 ((var p = (class-instance Point () (22 44)))
  (var q = (move (p)))
  )
 [(p expired)
  (q (my box Heap-addr2))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 44))
  (Heap-addr2 (box 1 ((class Point) ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
  ]
 []
 the-Zero-value)

(; Moving something that is lent creates a sublease.
 dada-seq-test
 ((var p = (class-instance Point () (22 44)))
  (var q = (lend (p)))
  (var r = (move (q)))
  )
 [(p (my box Heap-addr2))
  (q ((lent Lease-id) box Heap-addr2))
  (r ((lent Lease-id1) box Heap-addr2))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 44))
  (Heap-addr2 (box 1 ((class Point) ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
  ]
 [(Lease-id (lent () Heap-addr2))
  (Lease-id1 (lent (Lease-id) Heap-addr2))]
 the-Zero-value)

(; Moving something that is shared clones the lease.
 dada-seq-test
 ((var p = (class-instance Point () (22 44)))
  (var q = (share (p)))
  (var r = (move (q)))
  )
 [(p (my box Heap-addr2))
  (q ((shared Lease-id) box Heap-addr2))
  (r ((shared Lease-id) box Heap-addr2))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 44))
  (Heap-addr2 (box 1 ((class Point) ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
  ]
 [(Lease-id (shared () Heap-addr2))]
 the-Zero-value)

(; Moving a (my String) value contained within a
 ; p: (lent Some<my Point>) gives a (lent String),
 ; subleased from `p`.
 dada-seq-test
 ((var some-point = (class-instance Some ((my Point ())) ((class-instance Point () (22 44)))))
  (var p = (lend (some-point)))
  (var r = (move (p value)))
  )
 [(some-point (my box Heap-addr3))
  (p ((lent Lease-id) box Heap-addr3))
  (r ((lent Lease-id1) box Heap-addr2))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 44))
  (Heap-addr2 (box 1 ((class Point) ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
  (Heap-addr3 (box 1 ((class Some) ((value (my box Heap-addr2))))))
  ]
 [(Lease-id (lent () Heap-addr3))
  (Lease-id1 (lent (Lease-id) Heap-addr2))]
 the-Zero-value)

(; Moving a (shared String) value contained within a
 ; p: (lent Some<my Point>) clones the shared string.
 dada-seq-test
 ((var point = (class-instance Point () (22 44)))
  (var shared-point = (share (point)))
  (var some-shared-point = (class-instance Some (((shared ((shared (point)))) Point ())) ((copy (shared-point)))))
  (var p = (lend (some-shared-point)))
  (var r = (move (p value)))
  )
 [(point (my box Heap-addr2))
  (shared-point ((shared Lease-id) box Heap-addr2))
  (some-shared-point (my box Heap-addr3))
  (p ((lent Lease-id1) box Heap-addr3))
  (r ((shared Lease-id) box Heap-addr2))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 44))
  (Heap-addr2 (box 1 ((class Point) ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
  (Heap-addr3 (box 1 ((class Some) ((value ((shared Lease-id) box Heap-addr2))))))
  ]
 [(Lease-id (shared () Heap-addr2))
  (Lease-id1 (lent () Heap-addr3))
  ]
 the-Zero-value)

(; Moving a (lent String) value contained within a
 ; p: (lent Some<my Point>) subleases the two lent variables.
 dada-seq-test
 ((var point = (class-instance Point () (22 44)))
  (var lent-point = (lend (point)))
  (var some-lent-point = (class-instance Some (((lent ((lent (point)))) Point ())) ((give (lent-point)))))
  (var p = (lend (some-lent-point)))
  (var r = (move (p value)))
  )
 [(point (my box Heap-addr2))
  (lent-point expired)
  (some-lent-point (my box Heap-addr3))
  (p ((lent Lease-id1) box Heap-addr3))
  (r ((lent Lease-id2) box Heap-addr2))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 44))
  (Heap-addr2 (box 1 ((class Point) ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
  (Heap-addr3 (box 1 ((class Some) ((value ((lent Lease-id) box Heap-addr2))))))
  ]
 [(Lease-id (lent () Heap-addr2))
  (Lease-id1 (lent () Heap-addr3))
  (Lease-id2 (lent (Lease-id Lease-id1) Heap-addr2))]
 the-Zero-value)
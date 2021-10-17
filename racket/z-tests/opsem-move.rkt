#lang racket

(require "../dada.rkt")

(; Moving something that is uniquely owned moves.
 dada-seq-test
 ((var p = (class-instance Point () (22 44)))
  (var q = (give (p)))
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
  (var r = (give (q)))
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
  (var r = (give (q)))
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
  (var r = (give (p value)))
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
  (var some-shared-point = (class-instance Some (((shared ((shared (point)))) Point ())) ((share (shared-point)))))
  (var p = (lend (some-shared-point)))
  (var r = (give (p value)))
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
  (var some-lent-point = (class-instance Some (((lent ((lent (point)))) Point ())) ((lend (point)))))
  (var p = (lend (some-lent-point)))
  (var r = (give (p value)))
  )
 [(point (my box Heap-addr2))
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

(; Test that we are able to move both a/b where both are lent,
 ; just as if we owned them. In this case, at least with code as is,
 ; they are not nulled out as they would be if they were owned values.
 ; I'm not sure if this is right or not -- but to specify the distinction requires
 ; reasoning not about the access permissions of the *value* (that is, the Some)
 ; but about the *location where the value is stored* (the field of pair) and I am
 ; trying to avoid that. It does require creating more subleases this way.
 ;
 ; But it fits the reasoning of:
 ;
 ; * You have lent access to `pair-lent.a`, so "giving" that is done by subleasing.
 dada-seq-test
 ((var some-a = (class-instance Some () (22)))
  (var some-b = (class-instance Some () (44)))
  (var pair-lent = (class-instance Pair () ((lend (some-a)) (lend (some-b)))))
  (var lent-a = (give (pair-lent a)))
  (var lent-b = (give (pair-lent b)))
  )
 [(some-a (my box Heap-addr1))
  (some-b (my box Heap-addr3))
  (pair-lent (my box Heap-addr4))
  (lent-a ((lent Lease-id2) box Heap-addr1))
  (lent-b ((lent Lease-id3) box Heap-addr3))
  ]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 ((class Some) ((value (our box Heap-addr))))))
  (Heap-addr2 (box 1 44))
  (Heap-addr3 (box 1 ((class Some) ((value (our box Heap-addr2))))))
  (Heap-addr4
   (box
    1
    ((class Pair)
     ((a ((lent Lease-id) box Heap-addr1))
      (b ((lent Lease-id1) box Heap-addr3))))))]
 [(Lease-id (lent () Heap-addr1))
  (Lease-id1 (lent () Heap-addr3))
  (Lease-id2 (lent (Lease-id) Heap-addr1))
  (Lease-id3 (lent (Lease-id1) Heap-addr3))]
 the-Zero-value)

(; Test that we are able to move both a/b from a lent origin,
 ; just as if we owned it (in which case those fields would be nulled out).
 dada-seq-test
 ((var pair-some = (class-instance Pair () ((class-instance Some () (22))
                                            (class-instance Some () (44)))))
  (var lent-pair = (lend (pair-some)))
  (var lent-a = (give (lent-pair a)))
  (var lent-b = (give (lent-pair b)))
  )
 [(pair-some (my box Heap-addr4))
  (lent-pair ((lent Lease-id) box Heap-addr4))
  (lent-a ((lent Lease-id1) box Heap-addr1))
  (lent-b ((lent Lease-id2) box Heap-addr3))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 ((class Some) ((value (our box Heap-addr))))))
  (Heap-addr2 (box 1 44))
  (Heap-addr3 (box 1 ((class Some) ((value (our box Heap-addr2))))))
  (Heap-addr4
   (box
    1
    ((class Pair)
     ((a (my box Heap-addr1))
      (b (my box Heap-addr3))))))]
 [(Lease-id (lent () Heap-addr4))
  (Lease-id1 (lent (Lease-id) Heap-addr1))
  (Lease-id2 (lent (Lease-id) Heap-addr3))]
 the-Zero-value)
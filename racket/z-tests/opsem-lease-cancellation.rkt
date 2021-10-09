#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require "../dada.rkt")

(; Test lease cancellation
 dada-seq-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (var vec2 = (lend (vec1)))
  (var vec3 = (lend (vec1)))
  (set (vec3 value0) = 44))
 [(vec1 (my box Heap-addr1))
  (vec2 expired)
  (vec3 ((lent Lease-id1) box Heap-addr1))
  ]
 [(Heap-addr1 (box 1 ((class Vec) ((value0 (our box Heap-addr2))))))
  (Heap-addr2 (box 1 44))]
 [(Lease-id1 (lent () Heap-addr1))]
 the-Zero-value)

(; Test lease cancellation on read--reading vec1
 ; cancels vec2/vec3
 dada-seq-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (var vec2 = (lend (vec1)))
  (var vec3 = (lend (vec1)))
  (var v = (copy (vec1 value0))))
 [(vec1 (my box Heap-addr1))
  (vec2 expired)
  (vec3 expired)
  (v (our box Heap-addr))
  ]
 [(Heap-addr (box 2 22))
  (Heap-addr1 (box 1 ((class Vec) ((value0 (our box Heap-addr))))))]
 []
 the-Zero-value)

(; Test lease cancellation on read--reading vec2
 ; cancels vec3
 dada-seq-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (var vec2 = (lend (vec1)))
  (var vec3 = (lend (vec2)))
  (var v = (copy (vec2 value0))))
 [(vec1 (my box Heap-addr1))
  (vec2 ((lent Lease-id) box Heap-addr1))
  (vec3 expired)
  (v (our box Heap-addr))
  ]
 [(Heap-addr (box 2 22))
  (Heap-addr1 (box 1 ((class Vec) ((value0 (our box Heap-addr))))))]
 [(Lease-id (lent () Heap-addr1))]
 the-Zero-value)

(; Test lent lease cancellation on drop
 dada-seq-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (seq [(var vec2 = (lend (vec1)))
        (var vec3 = (lend (vec2)))])
  )
 [(vec1 (my box Heap-addr1))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 ((class Vec) ((value0 (our box Heap-addr))))))]
 [; Leases are gone now, as the lent refs have been dropped.
  ]
 the-Zero-value)

(; Test shared lease cancellation on drop
 dada-seq-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (seq [(var vec2 = (share (vec1)))
        (var vec3 = (share (vec2)))])
  )
 [(vec1 (my box Heap-addr1))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 ((class Vec) ((value0 (our box Heap-addr))))))]
 [; Leases are not gone now, as the sharing may have propagated!
  (Lease-id (shared () Heap-addr1))
  ]
 the-Zero-value)

(; Test shared lease cancellation on drop
 dada-full-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (seq [(var vec2 = (share (vec1)))
        (var vec3 = (share (vec2)))])
  )
 []
 []
 the-Zero-value)

#;(; Test shared lease cancellation on drop
   dada-seq-test
   ((var vec1 = (class-instance Vec (int) (22)))
    (var vec2 = (share (vec1)))
    (set (vec1 value0) = 44)
    (copy (vec2 value0))
    )
   [(vec1 (my box Heap-addr1)) (vec2 expired)]
   [(Heap-addr1 (box 1 ((class Vec) ((value0 (our box Heap-addr2))))))
    (Heap-addr2 (box 1 44))]
   []
   (copy (vec2 value0)))

#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         "../dada.rkt")

(; Test lease cancellation
 dada-seq-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (var vec2 = (lend (vec1)))
  (var vec3 = (lend (vec1)))
  (set (vec3 value0) = 44))
 [(vec1 (my box Heap-addr))
  (vec2 expired)
  (vec3 ((leased Lease-id1) box Heap-addr))
  ]
 [(Heap-addr (box 1 ((class Vec) ((value0 44)))))]
 [(Lease-id1 (borrowed () Heap-addr))]
 0)

(; Test lease cancellation on read--reading vec1
 ; cancels vec2/vec3
 dada-seq-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (var vec2 = (lend (vec1)))
  (var vec3 = (lend (vec1)))
  (var v = (copy (vec1 value0))))
 [(vec1 (my box Heap-addr))
  (vec2 expired)
  (vec3 expired)
  (v 22)
  ]
 [(Heap-addr (box 1 ((class Vec) ((value0 22)))))]
 []
 0)

(; Test lease cancellation on read--reading vec2
 ; cancels vec3
 dada-seq-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (var vec2 = (lend (vec1)))
  (var vec3 = (lend (vec2)))
  (var v = (copy (vec2 value0))))
 [(vec1 (my box Heap-addr))
  (vec2 ((leased Lease-id) box Heap-addr))
  (vec3 expired)
  (v 22)
  ]
 [(Heap-addr (box 1 ((class Vec) ((value0 22)))))]
 [(Lease-id (borrowed () Heap-addr))]
 0)

(; Test borrowed lease cancellation on drop
 dada-seq-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (seq [(var vec2 = (lend (vec1)))
        (var vec3 = (lend (vec2)))])
  )
 [(vec1 (my box Heap-addr))]
 [(Heap-addr (box 1 ((class Vec) ((value0 22)))))]
 [; Leases are gone now, as the borrowed refs have been dropped.
  ]
 0)

(; Test shared lease cancellation on drop
 dada-seq-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (seq [(var vec2 = (share (vec1)))
        (var vec3 = (share (vec2)))])
  )
 [(vec1 (my box Heap-addr))]
 [(Heap-addr (box 1 ((class Vec) ((value0 22)))))]
 [; Leases are not gone now, as the sharing may have propagated!
  (Lease-id (shared () Heap-addr))
  ]
 0)

(; Test shared lease cancellation on drop
 dada-full-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (seq [(var vec2 = (share (vec1)))
        (var vec3 = (share (vec2)))])
  )
 []
 []
 0)

#;(; Test shared lease cancellation on drop
 dada-seq-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (var vec2 = (share (vec1)))
  (set (vec1 value0) = 44)
  (copy (vec2 value0))
  )
 [(vec1 (my box Heap-addr)) (vec2 expired)]
 [(Heap-addr (box 1 ((class Vec) ((value0 44)))))]
 []
 (copy (vec2 value0)))
 
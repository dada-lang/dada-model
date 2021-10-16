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
  (var v = (share (vec1 value0))))
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
  (var v = (share (vec2 value0))))
 [(vec1 (my box Heap-addr1))
  (vec2 ((lent Lease-id) box Heap-addr1))
  (vec3 expired)
  (v (our box Heap-addr))
  ]
 [(Heap-addr (box 2 22))
  (Heap-addr1 (box 1 ((class Vec) ((value0 (our box Heap-addr))))))]
 [(Lease-id (lent () Heap-addr1))]
 the-Zero-value)

(; Test lent leases are not called when lent ref is dropped (see opsem-lent for an example
 ; of why)
 dada-seq-test
 ((var vec1 = (class-instance Vec (int) (22)))
  (seq [(var vec2 = (lend (vec1)))
        (var vec3 = (lend (vec2)))])
  )
 [(vec1 (my box Heap-addr1))]
 [(Heap-addr (box 1 22))
  (Heap-addr1 (box 1 ((class Vec) ((value0 (our box Heap-addr))))))]
 [; leases are not yet dropped; once vec1 is dropped, they will be
  (Lease-id (lent () Heap-addr1))
  (Lease-id1 (lent (Lease-id) Heap-addr1))]
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
 [; Lease is not gone now, as the sharing may have propagated!
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
    (share  (vec2 value0))
    )
   [(vec1 (my box Heap-addr1)) (vec2 expired)]
   [(Heap-addr1 (box 1 ((class Vec) ((value0 (our box Heap-addr2))))))
    (Heap-addr2 (box 1 44))]
   []
   (share  (vec2 value0)))

(; * Share pair -> p
 ; * Share p a -> q
 ; * Write p b
 ;
 ; FIXME-- This cancels p which in turn cancels q.
 ;         Is this correct? It does match Rust.
 dada-seq-test
 ((var pair = (class-instance Pair
                              ((my Point ())
                               (my Point ()))
                              ((class-instance Point () (22 44))
                               (class-instance Point () (66 88)))))
  (var p = (share (pair)))
  (var q = (share (p a)))
  (set (pair b y) = 99)
  )
 ((pair (my box Heap-addr6))
  (p expired)
  (q expired)
  )
 ((Heap-addr (box 1 22))
  (Heap-addr1 (box 1 44))
  (Heap-addr2
   (box
    1
    ((class Point) ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
  (Heap-addr3 (box 1 66))
  (Heap-addr5
   (box
    1
    ((class Point) ((x (our box Heap-addr3)) (y (our box Heap-addr7))))))
  (Heap-addr6
   (box 1 ((class Pair) ((a (my box Heap-addr2)) (b (my box Heap-addr5))))))
  (Heap-addr7 (box 1 99)))
 ()
 the-Zero-value)

(; * Share pair -> p
 ; * Share pair a -> q
 ; * Write p b
 ;
 ; Cancels p but not q.
 dada-seq-test
 ((var pair = (class-instance Pair
                              ((my Point ())
                               (my Point ()))
                              ((class-instance Point () (22 44))
                               (class-instance Point () (66 88)))))
  (var p = (share (pair)))
  (var q = (share (pair a)))
  (set (pair b y) = 99)
  )
 ((pair (my box Heap-addr6))
  (p expired)
  (q ((shared Lease-id1) box Heap-addr2))
  )
 ((Heap-addr (box 1 22))
  (Heap-addr1 (box 1 44))
  (Heap-addr2
   (box
    1
    ((class Point) ((x (our box Heap-addr)) (y (our box Heap-addr1))))))
  (Heap-addr3 (box 1 66))
  (Heap-addr5
   (box
    1
    ((class Point) ((x (our box Heap-addr3)) (y (our box Heap-addr7))))))
  (Heap-addr6
   (box 1 ((class Pair) ((a (my box Heap-addr2)) (b (my box Heap-addr5))))))
  (Heap-addr7 (box 1 99)))
 ((Lease-id1 (shared () Heap-addr2)))
 the-Zero-value)

(; NB: Reading `point x` expires both `lent-point` and `shared-point2`
 dada-seq-test
 [(var point = (class-instance Point () (22 44)))
  (var lent-point = (lend (point)))
  (var some = (class-instance Some
                              (((lent ((lent (point)))) Point ()))
                              ((give (lent-point)))))
  (var shared-some = (share (some)))
  (var shared-point2 = (share (shared-some value)))
  (share (point x))
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
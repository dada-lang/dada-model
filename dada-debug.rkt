#lang racket
(require redex)
(require "racket/dada.rkt")

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
 [(Heap-addr (box 1 ((class Point) ((x 22) (y 44)))))
  (Heap-addr1 (box 1 ((class Some) ((value ((lent Lease-id) box Heap-addr))))))
  ]
 [(Lease-id (lent () Heap-addr))
  (Lease-id1 (lent () Heap-addr1))
  (Lease-id2 (lent (Lease-id1 Lease-id) Heap-addr))]
 0)

#;((((String (class () ()))
     (Pair (class ((A out) (B out)) ((var a (my A)) (var b (my B)))))
     (Vec (class ((E out)) ((var value0 (my E)))))
     (Fn (class ((A in) (R out)) ()))
     (Cell (class ((T inout)) ((atomic value (my T)))))
     (Character
      (class () ((var hp int) (shared name (my String ())) (var ac int))))
     (ShVar (class ((T in)) ((var shv (our T)))))
     (Message
      (class ((E out))
        ((shared vec (my Vec ((my E))))
         (var element ((shared ((shared (vec)))) E)))))
     (Some (class ((E out)) ((var value (my E)))))
     (Option (class ((T out)) ()))
     (Point (class () ((shared x int) (shared y int)))))
    ())
   ((((r ((lent Lease-id2) box Heap-addr))
      (p ((lent Lease-id1) box Heap-addr1))
      (some-lent-point (my box Heap-addr1))
      (lent-point expired)
      (point (my box Heap-addr)))
     ())
    ((Zero (box 1 0))
     (Heap-addr (box 1 ((class Point) ((x 22) (y 44)))))
     (Heap-addr1
      (box 1 ((class Some) ((value ((lent Lease-id) box Heap-addr)))))))
    ((Lease-id (lent () Heap-addr))
     (Lease-id1 (lent () Heap-addr1))
     (Lease-id2 (lent (Lease-id1 Lease-id) Heap-addr))))
   (seq-pushed (0)))
#lang racket
(require "../dada.rkt")

(; async fn main() {
 ;     var p = Point(x: 22, y: 44)
 ;     print("The point is {p}").await
 ;     print("The point is ({p.x}, {p.y})").await
 ;     p.x := 33
 ;     p.x += 1
 ;     print("The point is now ({p.x}, {p.y})").await
 ; }
 ;
 ; // prints:
 ; // The point is Point(x: 22, y: 44)
 ; // The point is (22, 44)
 ; // The point is now (34, 44)
 dada-seq-test
 [(var p = (class-instance Point () (22 44)))
  (share (p))
  (set (p x) = 33)
  (share (p x))
  ]
 [(p (my box Heap-addr2))]
 [(Heap-addr1 (box 1 44))
  (Heap-addr2
   (box
    1
    ((class Point) ((x (our box Heap-addr3)) (y (our box Heap-addr1))))))
  (Heap-addr3 (box 2 33))]
 []
 (our box Heap-addr3))

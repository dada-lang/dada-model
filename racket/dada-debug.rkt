#lang racket
(require redex)
(require "dada.rkt")

(dada-check-pass
 ; Can read shared atomic fields if we ARE in an atomic section.
 ;
 ; {
 ;   var cell = ShVar(Cell(22))
 ;   var tmp = atomic { copy cell.shv.value }
 ; }
 program_test
 (seq (
       (var cell = (class-instance ShVar ((my Cell (int))) ((class-instance Cell (int) (22)))))
       (var tmp = (atomic (copy (cell shv value))))
       )))
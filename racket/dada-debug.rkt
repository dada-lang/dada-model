#lang racket
(require redex)
(require "dada.rkt")

  
(dada-pretty-print-ty
 ; Can't move from borrowed reference
 ;
 ; {
 ;   var char: my Character = Character(22, "Achilles", 44)
 ;   var p: borrowed(char) Character = lend char;
 ;   var q: my String = give p.name;
 ; }
 (seq ((var (char (my Character ())) = (class-instance Character () (22 (class-instance String () ()) 44)))
       (var (p (my borrowed ((borrowed (char))) (my Character ()))) = (lend (char)))
       (give (p name))
       ))
 )

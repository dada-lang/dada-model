#lang racket
(require redex)
(require "dada.rkt")

  
(dada-pretty-print
 ; {
 ;   var v: Vec<String> = Vec("foo");
 ;   var s: shared(v) String = share v[0];
 ;   var m: Message<String> = Message(v, s);
 ; }
 (seq ((var (v (my Vec ((my String ())))) = (class-instance Vec ((my String ())) ((class-instance String () ()))))
       (var (v2 (my Vec ((my String ())))) = (class-instance Vec ((my String ())) ((class-instance String () ()))))
       (var (s ((shared ((shared (v)))) String ())) = (share (v value0)))
       (var (m (my Message ((my String ())))) = (class-instance Message ((my String ())) ((give (v)) (give (s)))))
       ))
 )

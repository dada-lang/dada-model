#lang racket
(require redex)
(require "dada.rkt")

  
(dada-check-pass
 ; We *should* be able to track the dependency on `v`
 ; when we have something SHARED.
 ;
 ; {
 ;   var v: my Vec<String> = Vec("foo");
 ;   var p: shared(v) Vec<String> = share v;
 ;   var v2 = v;
 ;   share p[0]; // type of `p` is now `shared(v2) Vec<String>`, hence valid
 ; }
 (seq ((var (v (my Vec ((my String ())))) = (class-instance Vec ((my String ())) ((class-instance String () ()))))
       (var (p ((shared ((shared (v)))) Vec (((shared ((shared (v)))) String ())))) = (share (v)))
       (var (v2 (my Vec ((my String ())))) = (give (v)))
       (share (p value0))
       ))
 )
 
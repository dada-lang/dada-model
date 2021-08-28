#lang racket
(require redex)
(require "../dada.rkt")

(; fn get_first<lease l, type E>(x: shared(l) Vec<E>) -> shared(x) E {
 ;     x[0]
 ; }
 ;
 ; {
 ;   var v: my Vec<String> = Vec("foo");
 ;   var p: shared(v) Vec<String> = share v;
 ;   var s: shared(v) String = get_first<shared(v), String>(p);
 ; }

 redex-let*
 Dada
 [(generic-decls (term ((l out) (E out))))
  (ty_return (term ((shared ((shared (x)))) E)))
  (ty_x (term ((shared (l)) Vec ((my E)))))
  (named-method-definition_get-first (term (get-first (fn (generic-decls ((x ty_x)) -> ty_return) = (give (x value0))))))
  (program (term (program-with-methods
                  program_test
                  named-method-definition_get-first
                  )))]
 (dada-check-pass
  program
  (seq ((var (v (my Vec ((my String ())))) = (class-instance Vec ((my String ())) ((class-instance String () ()))))
        (var (p ((shared ((shared (v)))) Vec (((shared ((shared (v)))) String ())))) = (share (v)))
        (var (s ((shared ((shared (v)))) String ())) =
             (call get-first
                   (((shared (v))) ((shared ((shared (v)))) String ()))
                   ((give (p)))))
        ))
  )
 )

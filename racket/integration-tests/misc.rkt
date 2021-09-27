#lang racket
(require redex)
(require "../dada.rkt")

(redex-let*
 Dada
 [(ty_my_string (term (my String ())))
  (expr_let (term (seq ((var s = (class-instance String () ()))))))
  (ty_our_string (term ((shared ()) String ())))
  (ty_pair_of_strings (term (my Pair (ty_my_string ty_my_string))))
  (mode_our (term (shared ())))
  (ty_our_pair_of_strings (term (mode_our Pair (ty_my_string ty_my_string))))
  (expr_new_string (term (class-instance String () ())))
  ] 

 (dada-check-fail
  ; Can't mutate fields of shared types.
  ;
  ; {
  ;   var pair: shared (String, String) = ("foo", "bar")
  ;   pair.a = "foo1" // ERRO
  ; }
  program_test
  (seq ((var pair = ((class-instance Pair
                                     (ty_my_string ty_my_string)
                                     (expr_new_string expr_new_string))
                     : ty_our_pair_of_strings))
        (set (pair a) = expr_new_string) ; invalidates `pair_a`
        )))

 (dada-check-fail
  ; Can't mutate shared fields.
  ;
  ; {
  ;   var point: my Point = Point(22, 33)
  ;   point.x = "foo1" // ERRO
  ; }
  program_test
  (seq ((var point = (class-instance Point () (22 33)))
        (set (point x) = 44)
        )))

 (dada-check-fail
  ; Can't mutate shared fields of owned types.
  ;
  ; {
  ;   var pair: my Character = Character(22, "Achilles", 44)
  ;   pair.name = "blah" // ERROR
  ; }
  program_test
  (seq ((var pair = (class-instance Character () (22 expr_new_string 44)))
        (set (pair name) = expr_new_string) ; invalidates `pair_a`
        )))


 (dada-check-pass
  ; Can borrow, mutate fields through borrow, and then give away
  ;
  ; {
  ;   var char: my Character = Character(22, "Achilles", 44)
  ;   var char1: borrowed Character = lend char;
  ;   char1.ac = 66
  ;   var tmp: my Character = give char
  ; }
  program_test
  (seq ((var char = (class-instance Character () (22 expr_new_string 44)))
        (var char1 = (lend (char)))
        (set (char1 ac) = 66)
        (var tmp = (give (char)))
        )))

 (dada-check-fail
  ; Cannot continue using borrow after giving away
  ;
  ; {
  ;   var char: my Character = Character(22, "Achilles", 44)
  ;   var char1: borrowed Character = lend char;
  ;   give char
  ;   char1.ac = 66
  ; }
  program_test
  (seq ((var char = (class-instance Character () (22 expr_new_string 44)))
        (var char1 = (lend (char)))
        (give (char))
        (set (char1 ac) = 66)
        )))

 (dada-check-fail
  ; Borrowing from a shared field is an error
  ;
  ; {
  ;   var char my Character = Character(22, "Achilles", 44)
  ;   lend char.name; // ERROR: Can't borrow from a shared field
  ; }
  program_test
  (seq ((var char = (class-instance Character () (22 expr_new_string 44)))
        (lend (char name)))))


 (dada-check-fail
  ; Can't write var fields if they are shared.
  ;
  ; {
  ;   var cell = ShVar(Character(22, "Achilles", 44))
  ;   cell.shv.ac = 66 // ERROR
  ; }
  program_test
  (seq ((var char =
             (class-instance ShVar ((my Character ()))
                             ((class-instance Character () (22 expr_new_string 44)))))
        (set (char shv ac) = 66)
        )))

 )
  
 




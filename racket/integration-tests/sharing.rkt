#lang racket
(require redex)
(require "../dada.rkt")

;; Tests related to tracking what data is shared and what is not,
;; and expiring shares after mutations etc.

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
  
 (redex-let*
  Dada
  [(place_pair-a (term (pair a)))
   (lease_shared-pair-a (term (shared place_pair-a)))
   (mode_shared-pair-a (term (shared (lease_shared-pair-a))))
   (ty_shared-pair-a-String (term (mode_shared-pair-a String ())))]

  (dada-check-pass
   ; Shared aliases are invalidated after assignment, and we
   ; can (e.g.) move the value that was shared from afterwards.
   ;
   ; {
   ;   var pair = ("foo", "bar")
   ;   var pair_a = share pair.a
   ;   give pair_a
   ;   give pair_a
   ;   pair.a = "foo1"
   ;   give pair
   ; }
   program_test
   (seq ((var pair = (class-instance Pair
                                     (ty_my_string ty_my_string)
                                     (expr_new_string expr_new_string)))
         (var pair-a = (share (pair a)))
         (copy (pair-a))
         (copy (pair-a))
         (set (pair a) = expr_new_string) ; invalidates `pair_a`
         (give (pair)))))

  
  (dada-check-fail
   ; Can't access shared data after underlying value is mutated.
   ;
   ; {
   ;   var pair = ("foo", "bar")
   ;   var pair_a = share pair.a
   ;   give pair_a
   ;   give pair_a
   ;   pair.a = "foo1"
   ;   give pair_a // ERROR
   ; }
   program_test
   (seq ((var pair = (class-instance Pair
                                     (ty_my_string ty_my_string)
                                     (expr_new_string expr_new_string)))
         (var pair-a = (share (pair a)))
         (give (pair-a))
         (give (pair-a))
         (set (pair a) = expr_new_string) ; invalidates `pair_a`
         (give (pair-a)))))
  )

 (dada-check-pass
  ; Can share one field and mutate another
  ;
  ; {
  ;   var char: my Character = Character(22, "Achilles", 44)
  ;   var name: shared(char.name) String = share char.name;
  ;   char.ac = 66
  ;   give name
  ; }
  program_test
  (seq ((var char = (class-instance Character () (22 expr_new_string 44)))
        (var name = (share (char name)))
        (set (char ac) = 66)
        (give (name))
        )))


 )
  
 




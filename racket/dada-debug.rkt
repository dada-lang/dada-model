#lang racket
(require redex)
(require "dada.rkt")

(redex-let*
 Dada
 [(ty_my_string (term (my String ())))
  (expr_let (term (seq ((var (s ty_my_string) = (class-instance String () ()))))))
  (ty_our_string (term ((shared ()) String ())))
  (ty_pair_of_strings (term (my Pair (ty_my_string ty_my_string))))
  (mode_our (term (shared ())))
  (ty_our_pair_of_strings (term (mode_our Pair (ty_my_string ty_my_string))))
  (expr_new_string (term (class-instance String () ())))
  ]


 (redex-let*
  Dada
  [(ty_my_Character (term (my Character ())))
   (ty_sh_String (term ((shared ((shared (char name)))) String ())))
   (ty_my_Pair (term (my Pair (ty_sh_String int))))]
  
  (dada-check-pass
     ; We are able to track the dependency on `tmp.a`
     ;
     ; {
     ;   var char: my Character = Character(22, "Achilles", 44)
     ;   var pair: my Pair<shared(char.name) String, int> = Pair(share char.name, 66);
     ;   var tmp: my Pair<my Character, shared(tmp.a.name) String> = Pair(give char, give pair.a);
     ; }
     (seq ((var (char ty_my_Character) = (class-instance Character () (22 expr_new_string 44)))
           (var (pair ty_my_Pair) = (class-instance Pair (ty_sh_String int) ((share (char name)) 66)))
           (var (tmp
                 (my Pair (ty_my_Character
                           ((shared ((shared (tmp a name)))) String ()))))
                = (class-instance Pair (ty_my_Character ((shared ((shared (in-flight a name)))) String ())) ((give (char)) (give (pair a)))))
           )))
  )
 )
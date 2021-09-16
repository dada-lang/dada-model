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

 (redex-let*
  Dada
  [(ty_my_Character (term (my Character ())))
   (ty_sh_String (term ((shared ((shared (char name)))) String ())))
   (ty_my_Pair (term (my Pair (ty_sh_String int))))]

  (dada-check-fail
   ; Giving away `char` invalidates `pair.a` (which is shared from `char`)
   ;
   ; {
   ;   var char: my Character = Character(22, "Achilles", 44)
   ;   var pair: my Pair<shared(char.name) String, int> = Pair(share char.name, 66);
   ;   give char; // invalidates pair
   ;   give pair.a; // ERROR
   ; }
   program_test
   (seq ((var char = (class-instance Character () (22 expr_new_string 44)))
         (var pair = (class-instance Pair (ty_sh_String int) ((share (char name)) 66)))
         (give (char))
         (give (pair a)))))

  (dada-check-pass
   ; ...but `pair.b` is still accessible
   ;
   ; {
   ;   var char: my Character = Character(22, "Achilles", 44)
   ;   var pair: my Pair<shared(char.name) String, int> = Pair(share char.name, 66);
   ;   give char; // invalidates pair
   ;   give pair.b;
   ; }
   program_test
   (seq ((var char = (class-instance Character () (22 expr_new_string 44)))
         (var pair = (class-instance Pair (ty_sh_String int) ((share (char name)) 66)))
         (give (char))
         (give (pair b)))))
  )
 
 (dada-check-fail
  ; Once we move both fields of a `Pair`, it is freed, so reinitializing its fields
  ; cannot be done independently.
  ;
  ; {
  ;   var pair = ("foo", "bar")
  ;   give pair.a
  ;   give pair.b
  ;   pair.a = "foo1" // ERROR
  ;   pair.b = "foo2"
  ;   give pair
  ; }
  ;
  ; FIXME. This could perhaps be accepted, but to do so would require tracking
  ; not only *definitely initialized* paths but "shallowly initialized" paths.
  ; When moving from `pair.b`, we would add `pair` to this set, and then when
  ; assigning to `pair.a`, the assignment would be legal.
  program_test
  (seq ((var pair = (class-instance Pair
                                    (ty_my_string ty_my_string)
                                    (expr_new_string expr_new_string)))
        (give (pair a))
        (give (pair b))
        (set (pair a) = expr_new_string)
        (set (pair b) = expr_new_string)
        (give (pair)))))

 (dada-check-pass
  ; Can move a field of a `Pair`, reinitialize it, and then move the entire pair.
  ;
  ; {
  ;   var pair = ("foo", "bar")
  ;   give pair.a
  ;   pair.a = "foo1"
  ;   give pair
  ; }
  program_test
  (seq ((var pair = (class-instance Pair
                                    (ty_my_string ty_my_string)
                                    (expr_new_string expr_new_string)))
        (give (pair a))
        (set (pair a) = expr_new_string)
        (give (pair)))))
 
 (dada-check-fail
  ; Once a `Pair` is moved, it must be completely reinitialized;
  ; the fields can't be assigned independently.
  ;
  ; {
  ;   var pair = ("foo", "bar")
  ;   give pair
  ;   pair.a = "foo1" // ERROR
  ;   pair.b = "foo2"
  ;   give pair
  ; }
  program_test
  (seq ((var pair = (class-instance Pair
                                    (ty_my_string ty_my_string)
                                    (expr_new_string expr_new_string)))
        (give (pair))
        (set (pair a) = expr_new_string)
        (set (pair b) = expr_new_string)
        (give (pair))))
  )

 (dada-check-fail
  ; Can't move a `Pair` whose fields were all moved but only `a` was reinitialized.
  ;
  ; {
  ;   var pair = ("foo", "bar")
  ;   give pair.a
  ;   give pair.b
  ;   pair.a = "foo1"
  ;   // pair.b = "foo2"
  ;   give pair
  ; } // ERROR
  program_test
  (seq ((var pair = (class-instance Pair
                                    (ty_my_string ty_my_string)
                                    (expr_new_string expr_new_string)))
        (give (pair a))
        (give (pair b))
        (set (pair a) = expr_new_string)
        #;(set (pair b) = expr_new_string)
        (give (pair)))))

 
 (dada-check-fail
  ; Can't move a `Pair` whose fields were all moved but only `b` was reinitialized.
  ;
  ; {
  ;   var pair = ("foo", "bar")
  ;   give pair.a
  ;   give pair.b
  ;   // pair.a = "foo1"
  ;   pair.b = "foo2"
  ;   give pair
  ; } // ERROR
  program_test
  (seq ((var pair = (class-instance Pair
                                    (ty_my_string ty_my_string)
                                    (expr_new_string expr_new_string)))
        (give (pair a))
        (give (pair b))
        #;(set (pair a) = expr_new_string)
        (set (pair b) = expr_new_string)
        (give (pair)))))
  
 (redex-let*
  Dada
  [(place_pair-a (term (pair a)))
   (lease_shared-pair-a (term (shared place_pair-a)))
   (mode_shared-pair-a (term (shared (lease_shared-pair-a))))
   (ty_shared-pair-a-String (term (mode_shared-pair-a String ())))]

  (dada-check-fail
   ; Giving a value of copy type is still giving it.
   ;
   ; {
   ;   var pair = ("foo", "bar")
   ;   var pair_a = share pair.a
   ;   give pair_a
   ;   give pair_a
   ; }
   program_test
   (seq ((var pair = (class-instance Pair
                                     (ty_my_string ty_my_string)
                                     (expr_new_string expr_new_string)))
         (var pair-a = (share (pair a)))
         (give (pair-a))
         (give (pair-a)))))

  (dada-check-fail
   ; Can't copy a value of affine type
   ;
   ; {
   ;   var s = "foo"
   ;   copy s
   ; }
   program_test
   (seq ((var s = expr_new_string)
         (copy (s)))))

  )

 )
  
 




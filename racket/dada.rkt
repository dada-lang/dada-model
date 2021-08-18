#lang racket
(require redex)
(require "grammar.rkt"
         "opsem.rkt"
         "type-system.rkt"
         "util.rkt")

;; TODO
;;
;; * ref classes/structs
;; * ref types
;; * interfaces and dyn types
;; * forall types
;; * existential types


;; random rules not to forget:
;;
;; - data cannot directly embed classes, or else we have to adjust is-affine-ty to walk data fields
;; -

(redex-let*
 Dada
 [(program program_test)
  (env_empty env_empty)
  (ty_my_string (term (my String ())))
  (expr_let (term (seq ((var (s ty_my_string) = (class-instance String () ()))))))
  (ty_our_string (term ((shared ()) String ())))
  (ty_pair_of_strings (term (my Pair (ty_my_string ty_my_string))))
  (mode_our (term (shared ())))
  (ty_our_pair_of_strings (term (mode_our Pair (ty_my_string ty_my_string))))
  (expr_new_string (term (class-instance String () ())))
  (Store_empty
   (term ((stack ())
          (heap ())
          (ref-table ()))))
  ]

 ;; dada program expected to type check and run successfully
 ;;
 ;; (we don't test execution yet)
 (define-syntax-rule
   (dada-check-pass expr-term)
   (test-judgment-holds
    (expr-drop
     program
     env_empty
     expr-term
     _)))

 (define-syntax-rule
   (dada-pretty-print-ty expr-term)
   (pretty-print (judgment-holds
                  (expr-ty
                   program
                   env_empty
                   expr-term
                   ty_out
                   _) ty_out)))

 (define-syntax-rule
   (dada-check-exec expr-term value-pattern)
   (begin
     (test-judgment-holds
      (expr-drop
       program
       env_empty
       expr-term
       _))
     (test-match-terms Dada (eval-expr program Store_empty expr-term) (value-pattern _))
     ))

 ;; dada program expected not to type check
 (define-syntax-rule
   (dada-check-fail expr-term)
   (test-judgment-false
    (expr-drop
     program
     env_empty
     expr-term
     _)))

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
   (seq ((var (char ty_my_Character) = (class-instance Character () (22 expr_new_string 44)))
         (var (pair ty_my_Pair) = (class-instance Pair (ty_sh_String int) ((share (char name)) 66)))
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
   (seq ((var (char ty_my_Character) = (class-instance Character () (22 expr_new_string 44)))
         (var (pair ty_my_Pair) = (class-instance Pair (ty_sh_String int) ((share (char name)) 66)))
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
  (seq ((var (pair ty_pair_of_strings) = (class-instance Pair
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
  (seq ((var (pair ty_pair_of_strings) = (class-instance Pair
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
  (seq ((var (pair ty_pair_of_strings) = (class-instance Pair
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
  (seq ((var (pair ty_pair_of_strings) = (class-instance Pair
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
  (seq ((var (pair ty_pair_of_strings) = (class-instance Pair
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

  (dada-check-pass
   ; Shared aliases are invalidated after assignment, and we
   ; can (e.g.) move the value.
   ;
   ; {
   ;   var pair = ("foo", "bar")
   ;   var pair_a = share pair.a
   ;   give pair_a
   ;   give pair_a
   ;   pair.a = "foo1"
   ;   give pair
   ; }
   (seq ((var (pair ty_pair_of_strings) = (class-instance Pair
                                                          (ty_my_string ty_my_string)
                                                          (expr_new_string expr_new_string)))
         (var (pair-a ty_shared-pair-a-String) = (share (pair a)))
         (give (pair-a))
         (give (pair-a))
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
   (seq ((var (pair ty_pair_of_strings) = (class-instance Pair
                                                          (ty_my_string ty_my_string)
                                                          (expr_new_string expr_new_string)))
         (var (pair-a ty_shared-pair-a-String) = (share (pair a)))
         (give (pair-a))
         (give (pair-a))
         (set (pair a) = expr_new_string) ; invalidates `pair_a`
         (give (pair-a)))))
  )

 (dada-check-fail
  ; Can't mutate fields of shared types.
  ;
  ; {
  ;   var pair: shared (String, String) = ("foo", "bar")
  ;   pair.a = "foo1" // ERRO
  ; }
  (seq ((var (pair ty_our_pair_of_strings) = (class-instance Pair
                                                             (ty_my_string ty_my_string)
                                                             (expr_new_string expr_new_string)))
        (set (pair a) = expr_new_string) ; invalidates `pair_a`
        )))

 (dada-check-fail
  ; Can't mutate fields of data types.
  ;
  ; {
  ;   var point: Point = Point(22, 33)
  ;   point.x = "foo1" // ERRO
  ; }
  (seq ((var (point (Point ())) = (data-instance Point () (22 33)))
        (set (point x) = 44)
        )))

 (dada-check-fail
  ; Can't mutate shared fields of owned types.
  ;
  ; {
  ;   var pair: my Character = Character(22, "Achilles", 44)
  ;   pair.name = "blah" // ERROR
  ; }
  (seq ((var (pair (my Character ())) = (class-instance Character () (22 expr_new_string 44)))
        (set (pair name) = expr_new_string) ; invalidates `pair_a`
        )))

 (dada-check-pass
  ; Can share one field and mutate another
  ;
  ; {
  ;   var char: my Character = Character(22, "Achilles", 44)
  ;   var name: shared(char.name) String = share char.name;
  ;   char.ac = 66
  ;   give name
  ; }
  (seq ((var (char (my Character ())) = (class-instance Character () (22 expr_new_string 44)))
        (var (name ((shared ((shared (char name)))) String ())) = (share (char name)))
        (set (char ac) = 66)
        (give (name))
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
  (seq ((var (char (my Character ())) = (class-instance Character () (22 expr_new_string 44)))
        (var (char1 (my borrowed ((borrowed (char))) (my Character ()))) = (lend (char)))
        (set (char1 ac) = 66)
        (var (tmp (my Character ())) = (give (char)))
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
  (seq ((var (char (my Character ())) = (class-instance Character () (22 expr_new_string 44)))
        (var (char1 (my borrowed ((borrowed (char))) (my Character ()))) = (lend (char)))
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
  (seq ((var (char (my Character ())) = (class-instance Character () (22 expr_new_string 44)))
        (lend (char name)))))

 (dada-check-pass
  ; Can mutate atomic fields if they are uniquely accessed.
  ;
  ; {
  ;   var cell = Cell(22)
  ;   cell.shv.value = 44
  ; }
  (seq ((var (cell-ch (my Cell (int))) = (class-instance Cell (int) (22)))
        (set (cell-ch value) = 44)
        )))

 (dada-check-fail
  ; Can't mutate atomic fields if they are shared
  ; and we are not in an atomic section.
  ;
  ;
  ; {
  ;   var cell = ShVar(Cell(22))
  ;   cell.shv.value = 44
  ; }
  (seq ((var (cell-ch (my ShVar ((my Cell (int))))) = (class-instance ShVar ((my Cell (int))) ((class-instance Cell (int) (22)))))
        (set (cell-ch shv value) = 44)
        )))

 (dada-check-pass
  ; Can read atomic fields if they are uniquely accessed.
  ;
  ; {
  ;   var cell = Cell(22)
  ;   give cell.value
  ; }
  (seq ((var (cell-ch (my Cell (int))) = (class-instance Cell (int) (22)))
        (give (cell-ch value))
        )))

 (dada-check-fail
  ; Can't read atomic fields if they are shared
  ; and we are not in an atomic section.
  ;
  ; {
  ;   var cell = ShVar(Cell(22))
  ;   give cell.shv.value // ERROR
  ; }
  (seq ((var (cell-ch (my ShVar ((my Cell (int))))) = (class-instance ShVar ((my Cell (int))) ((class-instance Cell (int) (22)))))
        (give (cell-ch shv value))
        )))

 (dada-check-fail
  ; Can't share atomic fields if they are shared
  ; and we are not in an atomic section.
  ;
  ; {
  ;   var cell = ShVar(Cell(22))
  ;   share cell.shv.value // ERROR
  ; }
  (seq ((var (cell-ch (my ShVar ((my Cell (int))))) = (class-instance ShVar ((my Cell (int))) ((class-instance Cell (int) (22)))))
        (share (cell-ch shv value))
        )))

 (dada-check-fail
  ; Cannot write shared atomic fields if we are not in an atomic section.
  ;
  ; {
  ;   var cell = ShVar(Cell(22))
  ;   cell.shv.value = 44 // ERROR
  ; }
  (seq ((var (cell (my ShVar ((my Cell (int))))) = (class-instance ShVar ((my Cell (int))) ((class-instance Cell (int) (22)))))
        (set (cell shv value) = 44)
        )))

 (dada-check-pass
  ; Can read shared atomic fields if we ARE in an atomic section.
  ;
  ; {
  ;   var cell = ShVar(Cell(22))
  ;   var tmp = atomic { give cell.shv.value }
  ; }
  (seq ((var (cell (my ShVar ((my Cell (int))))) = (class-instance ShVar ((my Cell (int))) ((class-instance Cell (int) (22)))))
        (var (tmp int) = (atomic (give (cell shv value))))
        )))

 (dada-check-pass
  ; Can share atomic fields if they are shared
  ; and we ARE in an atomic section.
  ;
  ; {
  ;   var cell = ShVar(Cell(22))
  ;   var tmp = atomic { share cell.shv.value }
  ; }
  (seq ((var (cell-ch (my ShVar ((my Cell (int))))) = (class-instance ShVar ((my Cell (int))) ((class-instance Cell (int) (22)))))
        (var (tmp int) = (atomic (share (cell-ch shv value))))
        )))

 (dada-check-pass
  ; Can write shared atomic fields if we ARE in an atomic section.
  ;
  ; {
  ;   var cell = ShVar(Cell(22))
  ;   atomic { cell.shv.value = 44 }
  ; }
  (seq ((var (cell (my ShVar ((my Cell (int))))) = (class-instance ShVar ((my Cell (int))) ((class-instance Cell (int) (22)))))
        (atomic (set (cell shv value) = 44))
        )))

 (redex-let*
  Dada
  [(ty_my_string (term (my String ())))
   (ty_my_Cell_string (term (my Cell (ty_my_string))))
   (ty_my_ShVar_Cell_string (term (my ShVar (ty_my_Cell_string))))
   (expr_new_Cell_string (term (class-instance Cell
                                               (ty_my_string)
                                               (expr_new_string))))
   (expr_new_ShVar_Cell_string (term (class-instance ShVar
                                                     (ty_my_Cell_string)
                                                     (expr_new_Cell_string))))]

  (dada-check-fail
   ; Cannot move affine data from a shared, atomic location.
   ;
   ; {
   ;   var cell = ShVar(Cell("foo"))
   ;   give cell.shv.value
   ; }
   (seq ((var (cell ty_my_ShVar_Cell_string) = expr_new_ShVar_Cell_string)
         (give (cell shv value))
         )))

  (dada-check-fail
   ; Cannot lend affine data from a shared, atomic location if we are not
   ; in an atomic section.
   ;
   ; {
   ;   var cell = ShVar(Cell("foo"))
   ;   lend cell.shv.value
   ; }
   (seq ((var (cell ty_my_ShVar_Cell_string) = expr_new_ShVar_Cell_string)
         (lend (cell shv value))
         )))
  
  (dada-check-fail
   ; Cannot move affine data from a shared location.
   ;
   ; {
   ;   var cell = ShVar(Cell("foo"))
   ;   atomic { give cell.shv.value }
   ; }
   (seq ((var (cell ty_my_ShVar_Cell_string) = expr_new_ShVar_Cell_string)
         (atomic (give (cell shv value)))
         )))

  (dada-check-fail
   ; Shared data that requires an atomic section cannot escape
   ; the atomic section
   ;
   ; {
   ;   var cell = ShVar(Cell("foo"))
   ;   var str = "bar"
   ;   var scell: shared(cell.shv.value, str) String = share str
   ;   atomic { scell = share cell.shv.value } // ERROR
   ; }
   (seq ((var (cell ty_my_ShVar_Cell_string) = expr_new_ShVar_Cell_string)
         (var (str ty_my_string) = expr_new_string)
         (var (scell ((shared ((shared (str)) (shared (cell shv value)))) String ())) = (share (str)))
         (atomic (set (scell) = (share (cell shv value))))
         )))

  (dada-check-pass
   ; Can lend shared atomic fields if we ARE in an atomic section.
   ;
   ; {
   ;   var cell = ShVar(Cell(22))
   ;   var v = atomic { lend cell.shv.value; 44}
   ; }
   (seq ((var (cell (my ShVar ((my Cell (int))))) = (class-instance ShVar ((my Cell (int))) ((class-instance Cell (int) (22)))))
         (var (v int) = (atomic (seq ((lend (cell shv value)) 44))))
         )))
  )

 (dada-check-fail
  ; Can't write var fields if they are shared.
  ;
  ; {
  ;   var cell = ShVar(Character(22, "Achilles", 44))
  ;   cell.shv.ac = 66 // ERROR
  ; }
  (seq ((var (char (my ShVar ((my Character ())))) =
             (class-instance ShVar ((my Character ()))
                             ((class-instance Character () (22 expr_new_string 44)))))
        (set (char shv ac) = 66)
        )))

 )
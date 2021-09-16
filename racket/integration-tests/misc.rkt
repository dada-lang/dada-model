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
  ; Can't mutate fields of data types.
  ;
  ; {
  ;   var point: Point = Point(22, 33)
  ;   point.x = "foo1" // ERRO
  ; }
  program_test
  (seq ((var point = (data-instance Point () (22 33)))
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

 (dada-check-pass
  ; Can mutate atomic fields if they are uniquely accessed.
  ;
  ; {
  ;   var cell = Cell(22)
  ;   cell.shv.value = 44
  ; }
  program_test
  (seq ((var cell-ch = (class-instance Cell (int) (22)))
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
  program_test
  (seq ((var cell-ch = (class-instance ShVar ((my Cell (int))) ((class-instance Cell (int) (22)))))
        (set (cell-ch shv value) = 44)
        )))

 (dada-check-pass
  ; Can read atomic fields if they are uniquely accessed.
  ;
  ; {
  ;   var cell = Cell(22)
  ;   give cell.value
  ; }
  program_test
  (seq ((var cell-ch = (class-instance Cell (int) (22)))
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
  program_test
  (seq ((var cell-ch = (class-instance ShVar ((my Cell (int))) ((class-instance Cell (int) (22)))))
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
  program_test
  (seq ((var cell-ch = (class-instance ShVar ((my Cell (int))) ((class-instance Cell (int) (22)))))
        (share (cell-ch shv value))
        )))

 (dada-check-fail
  ; Cannot write shared atomic fields if we are not in an atomic section.
  ;
  ; {
  ;   var cell = ShVar(Cell(22))
  ;   cell.shv.value = 44 // ERROR
  ; }
  program_test
  (seq ((var cell = (class-instance ShVar ((my Cell (int))) ((class-instance Cell (int) (22)))))
        (set (cell shv value) = 44)
        )))

 (dada-check-pass
  ; Can read shared atomic fields if we ARE in an atomic section.
  ;
  ; {
  ;   var cell = ShVar(Cell(22))
  ;   var tmp = atomic { copy cell.shv.value }
  ; }
  program_test
  (seq ((var cell = (class-instance ShVar ((my Cell (int))) ((class-instance Cell (int) (22)))))
        (var tmp = (atomic (copy (cell shv value))))
        )))

 (dada-check-pass
  ; Can share atomic fields if they are shared
  ; and we ARE in an atomic section.
  ;
  ; {
  ;   var cell = ShVar(Cell(22))
  ;   var tmp = atomic { share cell.shv.value }
  ; }
  program_test
  (seq ((var cell-ch = (class-instance ShVar ((my Cell (int))) ((class-instance Cell (int) (22)))))
        (var tmp = (atomic (share (cell-ch shv value))))
        )))

 (dada-check-pass
  ; Can write shared atomic fields if we ARE in an atomic section.
  ;
  ; {
  ;   var cell = ShVar(Cell(22))
  ;   atomic { cell.shv.value = 44 }
  ; }
  program_test
  (seq ((var cell = (class-instance ShVar ((my Cell (int))) ((class-instance Cell (int) (22)))))
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
   program_test
   (seq ((var cell = expr_new_ShVar_Cell_string)
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
   program_test
   (seq ((var cell = expr_new_ShVar_Cell_string)
         (lend (cell shv value))
         )))
  
  (dada-check-fail
   ; Cannot move affine data from a shared location.
   ;
   ; {
   ;   var cell = ShVar(Cell("foo"))
   ;   atomic { give cell.shv.value }
   ; }
   program_test
   (seq ((var cell = expr_new_ShVar_Cell_string)
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
   program_test
   (seq ((var cell = expr_new_ShVar_Cell_string)
         (var str = expr_new_string)
         (var scell = (share (str)))
         (atomic (set (scell) = (share (cell shv value))))
         )))

  (dada-check-pass
   ; Can lend shared atomic fields if we ARE in an atomic section.
   ;
   ; {
   ;   var cell = ShVar(Cell(22))
   ;   var v = atomic { lend cell.shv.value; 44}
   ; }
   program_test
   (seq ((var cell = (class-instance ShVar ((my Cell (int))) ((class-instance Cell (int) (22)))))
         (var v = (atomic (seq ((lend (cell shv value)) 44))))
         )))
  )

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
  
 




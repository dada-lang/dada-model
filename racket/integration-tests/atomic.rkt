#lang racket
(require redex)
(require "../dada.rkt")

(redex-let*
 Dada
 [(ty_my_string (term (my String ())))
  (expr_let (term (seq ((var s = (class-instance String () ()))))))
  (ty_our_string (term ((shared ()) String ())))
  (ty_pair_of_strings (term (my Pair (ty_my_string ty_my_string))))
  (perms_our (term (shared ())))
  (ty_our_pair_of_strings (term (perms_our Pair (ty_my_string ty_my_string))))
  (expr_new_string (term (class-instance String () ())))
  ]

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


 )






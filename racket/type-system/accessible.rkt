#lang racket
(require redex "../grammar.rkt" "../util.rkt" "lang.rkt" "lease-implication.rkt")
(provide place-accessible)

(define-judgment-form dada-type-system
  #:mode (read-accessible I I I I I)
  #:contract (read-accessible program_in env_in place_in atomic?)
  #:inv (all? (defined? (place-ty program_in env_in place_in)))

  ; In an atomic section, we can read anything
  [--------------------------
   (read-accessible program env place (atomic))]

  ; Outside of an atomic section, can only read atomic fields
  ; if we have a unique place.
  [(where atomic (field-mutability program env (x f_0 ...) f_1))
   (is-unique program env (x f_0 ...))
   --------------------------
   (read-accessible program env (x f_0 ... f_1) ())]

  ; Immut/var fields can be read outside an atomic section,
  ; so long as their parents can be read too.
  [(where (_ c _) (place-ty program env (x f_0 ...)))
   (side-condition? (not-atomic? (field-mutability program env (x f_0 ...) f_1)))
   (read-accessible program env (x f_0 ...) ())
   --------------------------
   (read-accessible program env (x f_0 ... f_1) ())]

  ; Local variables are never directly aliased, and hence
  ; always readable out of an atomic section.
  [--------------------------
   (read-accessible program env (x) ())]
  )

;; assignable program env ty_source ty_target
;;
;; Holds if a value of type `ty_source` can be assigned to a
;; place of type `ty_target`.
(define-judgment-form dada-type-system
  #:mode (place-accessible I I I I I)
  #:contract (place-accessible program_in env_in action-kind place_in atomic?)
  #:inv (all? (defined? (place-ty program_in env_in place_in)))

  ; Any sort of access to a local variable is always legal
  [--------------------------
   (place-accessible program env action-kind (x) ())]

  [(place-accessible program env read (x_0 f_0 ...) atomic?)
   (side-condition (unique-value? program env (x_0 f_0 ...)))
   --------------------------
   (place-accessible program env read (x_0 f_0 ... f_1) atomic?)
   ]

  ; Accessing an atomic field of a shared value
  ; requires an atomic section (true for read or write).
  [(where place_0 (x_0 f_0 ...))
   (where (mode_0 c_0 _) (place-ty program env place_0))
   (where (name is-shared? #t) (any? (shared-place? program env place_0)
                                     (shared-mode? mode_0)))
   (where atomic (class-field-mutability program c_0 f_1))
   --------------------------
   (place-accessible program env _ (x_0 f_0 ... f_1) (atomic))
   ]

  ; Reading a non-atomic field is legal whenever reading the
  ; prefix is legal.
  [(where place_0 (x_0 f_0 ...))
   (where (_ c _) (place-ty program env place_0))
   (side-condition (class-field-non-atomic? program c f_1))
   (place-accessible program env read place_0 atomic?)
   --------------------------
   (place-accessible program env read (x_0 f_0 ... f_1) atomic?)
   ]

  ; Writing a var field is legal whenever writing the
  ; prefix is legal.
  [(where place_0 (x_0 f_0 ...))
   (where (my c _) (place-ty program env place_0))
   (side-condition (class-field-mutable? program c f_1))
   (place-accessible program env write place_0 atomic?)
   --------------------------
   (place-accessible program env write (x_0 f_0 ... f_1) atomic?)
   ]

  ; Writing an atomic field is legal when the prefix is shared
  ; and the field is declared as atomic.
  [(where place_0 (x_0 f_0 ...))
   (where ((shared _) c _) (place-ty program env place_0))
   (where atomic (class-field-mutability program c f_1))
   --------------------------
   (place-accessible program env write (x_0 f_0 ... f_1) (atomic))
   ]

  
  )

;; shared-place? program env place
;;
;; True if the place reached by P is (potentially) reachable via
;; some other, independent place P_1.
;;
;; Two places P_0, P_1 are *independent* if using P_0 does not
;; invalidate using P_1 and vice-versa.
(define-metafunction
  dada-type-system
  shared-place? : program env place -> boolean

  [(shared-place? program env (x f_0 ... f_1 f_2 ...))
   ; Accessing a field of a shared value is shared.
   #t
   (where place_0 ((x f_0) ...))
   (where ((shared _) c _) (place-ty program env place_0))

   or

   ; Accessing a shared field of a value is shared.
   #t
   (where place_0 ((x f_0) ...))
   (where (mode c _) (place-ty program env place_0))
   (where #t (class-field-shared? program c f_1))
   ]

  
  [(shared-place? _ _ _)
   ; Everything else is unique.
   #f]
  
  )
  
(redex-let*
 dada-type-system
 [(program program_test)

  (ty_my_character (term (my Character ())))
  
  (ty_my_string (term (my String ())))
  (ty_my_pair_of_my_strings (term (my Pair (ty_my_string ty_my_string))))
  (ty_my_pair_char_str (term (my Pair (ty_my_character ty_my_string))))
  
  (ty_our_string (term (our String ())))
  (ty_our_pair_of_my_strings (term (our Pair (ty_my_string ty_my_string))))
  
  (env (term (test-env (pair-ch ty_my_pair_char_str)
                       (cell-ch (my Cell (ty_my_character)))
                       (shvar-cell-ch (my ShVar ((my Cell (ty_my_character)))))
                       (shvar-cell-int (my ShVar ((my Cell (int)))))
                       )))
  ]

 (define-syntax-rule
   (dada-test-accessible-unatomic action-term place-term)
   (test-judgment-holds
    (place-accessible
     program
     env
     action-term
     place-term
     (side-condition atomic? (equal? (term ()) (term atomic?))))))

 (define-syntax-rule
   (dada-test-accessible-atomic action-term place-term)
   (test-judgment-holds
    (place-accessible
     program
     env
     action-term
     place-term
     (side-condition atomic? (equal? (term (atomic)) (term atomic?))))))

 (define-syntax-rule
   (dada-test-not-accessible action-term place-term)
   (test-judgment-false
    (place-accessible
     program
     env
     action-term
     place-term
     _)))

 ; the hp field is declared as var, hence can be read and written
 (dada-test-accessible-unatomic read (pair-ch a hp))
 (dada-test-accessible-unatomic write (pair-ch a hp))

 ; the name field is declared as shared, hence can be read  but not written
 (dada-test-accessible-unatomic read (pair-ch a name))
 (dada-test-not-accessible write (pair-ch a name))

 ; Atomic fields are accessible without atomic when unique
 (dada-test-accessible-unatomic read (cell-ch value hp))
 (dada-test-accessible-unatomic write (cell-ch value hp))

 ; But not if shared
 (dada-test-accessible-atomic read (shvar-cell-ch shv value hp))
 (dada-test-accessible-atomic write (shvar-cell-ch shv value hp))

 (dada-test-accessible-atomic read (shvar-cell-int shv value))
 (dada-test-accessible-atomic write (shvar-cell-int shv value))
 )
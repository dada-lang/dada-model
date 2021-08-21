#lang racket
(require redex
         "../grammar.rkt"
         "../util.rkt"
         "lang.rkt"
         "lease-implication.rkt"
         "type-manip.rkt")
(provide read-accessible
         write-accessible
         atomic-required-for-read?
         atomic-required-for-write?
         place-uniquely-owns-its-location)

(define-judgment-form dada-type-system
  #:mode (atomic-required-for-read? I I I O)
  #:contract (atomic-required-for-read? program_in env_in place_in atomic?)

  [(side-condition ,(not (judgment-holds (read-accessible program env place ()))))
   --------------------------
   (atomic-required-for-read? program env place (atomic))]

  [(read-accessible program env place ())
   --------------------------
   (atomic-required-for-read? program env place ())]
  )

(define-judgment-form dada-type-system
  ;; read-acceessible program env place atomic?
  ;;
  ;; Determines whether it is valid to read `place`;
  ;; `atomic?` determines whether we are currently in
  ;; an atomic section. This judgment assumes `place` is initialized. 
  ;;
  ;; In general reads of initialized data are permitted. The main
  ;; exception is that reading shared, atomic fields requires an
  ;; atomic section.
  
  #:mode (read-accessible I I I I)
  #:contract (read-accessible program_in env_in place_in atomic?)
  #:inv (all? (defined? (place-ty program_in env_in place_in)))

  ; In an atomic section, we can read anything
  [--------------------------
   (read-accessible program env place (atomic))]

  ; Outside of an atomic section, can only read an atomic field `f_1`
  ; if we have a unique access to it.
  [(where atomic (place-field-mutability program env (x f_0 ...) f_1))
   (place-has-unique-access-to-its-fields program env (x f_0 ...))
   --------------------------
   (read-accessible program env (x f_0 ... f_1) ())]

  ; Immut fields can be read outside an atomic section,
  ; so long as their parents can be read too.
  [(where shared (place-field-mutability program env (x f_0 ...) f_1))
   (read-accessible program env (x f_0 ...) ())
   --------------------------
   (read-accessible program env (x f_0 ... f_1) ())]

  ; Var fields can be read outside an atomic section,
  ; so long as their parents can be read too.
  [(where var (place-field-mutability program env (x f_0 ...) f_1))
   (read-accessible program env (x f_0 ...) ())
   --------------------------
   (read-accessible program env (x f_0 ... f_1) ())]
  
  ; Local variables are never directly aliased, and hence
  ; always readable out of an atomic section.
  [--------------------------
   (read-accessible program env (x) ())]
  )

(define-judgment-form dada-type-system
  ;; atomic-required-for-write? program env place atomic?
  ;;
  ;; Determines whether an atomic section is required to write to `place`.
  
  #:mode (atomic-required-for-write? I I I O)
  #:contract (atomic-required-for-write? program_in env_in place_in atomic?)

  [(side-condition ,(not (judgment-holds (write-accessible program env place ()))))
   --------------------------
   (atomic-required-for-write? program env place (atomic))]

  [(write-accessible program env place ())
   --------------------------
   (atomic-required-for-write? program env place ())]
  )

(define-judgment-form dada-type-system
  ;; write-accessible program env place atomic?
  ;;
  ;; Determines whether `place` can be written (assuming everything is
  ;; initialized). `atomic?` indicagtes whether or not we are in an
  ;; atomic section.
  ;;
  ;; General rules:
  ;;
  ;; * writes are illegal when you pass through a shared context
  ;; * unless the field is atomic
  
  #:mode (write-accessible I I I I)
  #:contract (write-accessible program_in env_in place_in atomic?)
  #:inv (all? (defined? (place-ty program_in env_in place_in)))

  ; Var fields can be written so long as
  ;
  ; (a) they have a unique access *from the parent place*
  ; (b) the parent place is itself writable
  ;
  ; Note that having unique access *from the parent place* is not
  ; the same as unique, since the parent place may be a shared atomic
  ; field.
  [(where var (place-field-mutability program env (x f_0 ...) f_1))
   (ty-has-unique-access-to-its-fields (place-ty program env (x f_0 ...)))
   (write-accessible program env (x f_0 ...) atomic?)
   --------------------------
   (write-accessible program env (x f_0 ... f_1) atomic?)]

  ; Inside an atomic section, can always write to atomic fields
  ; (even if, e.g., we may not be able to write to their parents).
  [(where atomic (place-field-mutability program env (x f_0 ...) f_1))
   --------------------------
   (write-accessible program env (x f_0 ... f_1) (atomic))]
  
  ; Outside of an atomic section, atomic fields behave like var fields.
  [(where atomic (place-field-mutability program env (x f_0 ...) f_1))
   (ty-has-unique-access-to-its-fields (place-ty program env (x f_0 ...)))
   (write-accessible program env (x f_0 ...) ())
   --------------------------
   (write-accessible program env (x f_0 ... f_1) ())]

  ; Local variables can be written in or out of an atomic section.
  [--------------------------
   (write-accessible program env (x) atomic?)]
  )

(define-judgment-form dada-type-system
  ;; place-has-unique-access-to-its-fields program env place
  ;;
  ;; True if the fields of `place` are uniquely reachable via `place`
  ;; (i.e., there is no other independent place that can reach those fields)
  
  #:mode (place-has-unique-access-to-its-fields I I I)
  #:contract (place-has-unique-access-to-its-fields program_in env_in place_in)
  #:inv (all? (defined? (place-ty program_in env_in place_in)))

  [(ty-has-unique-access-to-its-fields (place-ty program env place))
   (place-names-unique-location program env place)
   --------------------------
   (place-has-unique-access-to-its-fields program env place)]
  )

(define-judgment-form dada-type-system
  ;; place-names-unique-location program env place
  ;;
  ;; True if place P names a unique memory location L (i.e., there is no
  ;; independent path P_1 that can reach L). Note that L may contain
  ;; a shared value.
  
  #:mode (place-names-unique-location I I I)
  #:contract (place-names-unique-location program_in env_in place_in)

  ; If a field is mutable or atomic, and we have a unique path to it,
  ; the user cannot lend out shared copies of it that we don't know about.
  [(place-has-unique-access-to-its-fields program env (x f_0 ...))
   (side-condition (mutable? (place-field-mutability program env (x f_0 ...) f_1)))
   --------------------------
   (place-names-unique-location program env (x f_0 ... f_1))]

  ; If a field is immutable, then the user may have shared its contents.
  ; But if we own the field, then we would be able to observe and cancel
  ; those shares, so in that case we can consider the locations unique.
  [(place-uniquely-owns-its-fields program env (x f_0 ...))
   (where shared (place-field-mutability program env (x f_0 ...) f_1))
   --------------------------
   (place-names-unique-location program env (x f_0 ... f_1))]

  ; Local variables are always unique.
  [--------------------------
   (place-names-unique-location program env (x))]
  )  

(define-judgment-form dada-type-system
  ;; ty-has-unique-access-to-its-fields ty
  ;;
  ;; True if a value of type `ty` has unique access to its fields.
  
  #:mode (ty-has-unique-access-to-its-fields I)
  #:contract (ty-has-unique-access-to-its-fields ty)

  [--------------------------
   (ty-has-unique-access-to-its-fields (dt params))]

  [--------------------------
   (ty-has-unique-access-to-its-fields (my c params))]

  [(ty-has-unique-access-to-its-fields ty)
   --------------------------
   (ty-has-unique-access-to-its-fields (my borrowed _ ty))]
  )

(define-judgment-form dada-type-system
  ;; place-uniquely-owns-its-fields program env place
  ;;
  ;; True if the current stack frame uniquely owns the fields of the
  ;; value stored in `place` (i.e., when `place` is dropped, its fields
  ;; will be too).
  
  #:mode (place-uniquely-owns-its-fields I I I)
  #:contract (place-uniquely-owns-its-fields program_in env_in place_in)

  [(ty-uniquely-owns-its-fields (place-ty program env place))
   (place-uniquely-owns-its-location program env place)
   --------------------------
   (place-uniquely-owns-its-fields program env place)]
  )

(define-judgment-form dada-type-system
  ;; place-uniquely-owns-its-location program env place
  ;;
  ;; True if the current stack frame uniquely owns the location named
  ;; by `place` (i.e., when the local variable that roots `place` is
  ;; dropped, the current contents of the location named by `place`
  ;; (if any) will be freed).
  
  #:mode (place-uniquely-owns-its-location I I I)
  #:contract (place-uniquely-owns-its-location program_in env_in place_in)

  [(place-uniquely-owns-its-fields program env (x f_0 ...))
   --------------------------
   (place-uniquely-owns-its-location program env (x f_0 ... f_1))]
  
  [--------------------------
   (place-uniquely-owns-its-location program env (x))]
  )

(define-judgment-form dada-type-system
  ;; ty-uniquely-owns-its-fields program env place
  ;;
  ;; True if a value of type `ty` uniquely owns its fields (i.e.,
  ;; when the value is dropped, its fields will be too).
  
  #:mode (ty-uniquely-owns-its-fields I)
  #:contract (ty-uniquely-owns-its-fields ty)

  [--------------------------
   (ty-uniquely-owns-its-fields (dt _))]

  [--------------------------
   (ty-uniquely-owns-its-fields (my c _))]
  )

(module+ test
  (redex-let*
   dada-type-system
   [(ty_my_character (term (my Character ())))
  
    (ty_my_string (term (my String ())))
    (ty_my_pair_of_my_strings (term (my Pair (ty_my_string ty_my_string))))
    (ty_my_pair_char_str (term (my Pair (ty_my_character ty_my_string))))
  
    (ty_our_string (term (our String ())))
    (ty_our_pair_of_my_strings (term (our Pair (ty_my_string ty_my_string))))
    ]

   (define-syntax-rule
     (dada-test place-term
                env-term
                (read-holds-atomic-term ...)
                (read-false-atomic-term ...)
                (write-holds-atomic-term ...)
                (write-false-atomic-term ...))
     (begin
       ; Uncomment this to log which tests fail:
       #;(pretty-print (term ("dada-test" place-term)))

       (test-judgment-holds
        (read-accessible
         program_test
         env-term
         place-term
         read-holds-atomic-term))
       ...
       (test-judgment-false
        (read-accessible
         program_test
         env-term
         place-term
         read-false-atomic-term))
       ...
       (test-judgment-holds
        (write-accessible
         program_test
         env-term
         place-term
         write-holds-atomic-term))
       ...
       (test-judgment-false
        (write-accessible
         program_test
         env-term
         place-term
         write-false-atomic-term))
       ...
      
       )
     )
 
   ; the hp field is declared as var, hence can be read and written
   (dada-test (pair-ch a hp)
              (test-env (pair-ch ty_my_pair_char_str))
              (() (atomic)) ; read in or out of atomic section
              ()        
              (() (atomic)) ; write in or out of atomic section
              ()
              )

   ; also for borrowed refs
   (dada-test (borrow-pair-ch a hp)
              (test-env (borrow-pair-ch (my borrowed () ty_my_pair_char_str)))
              (() (atomic)) ; read in or out of atomic section
              ()        
              (() (atomic)) ; write in or out of atomic section
              ()
              )

   ; the name field is declared as shared, hence can be read but not written
   (dada-test (pair-ch a name)
              (test-env (pair-ch ty_my_pair_char_str))
              (() (atomic)) ; read in or out of atomic section
              ()
              ()
              (() (atomic)) ; cannot write in or out of atomic section
              )

   ; ...true even when borrowed
   (dada-test (pair-ch a name)
              (test-env (pair-ch (my borrowed () ty_my_pair_char_str)))
              (() (atomic)) ; read in or out of atomic section
              ()
              ()
              (() (atomic)) ; cannot write in or out of atomic section
              )

   ; the hp field is declared as var, which is immutable when shared
   (dada-test (shvar-ch shv hp)
              (test-env (shvar-ch (my ShVar (ty_my_character))))
              (() (atomic)) ; read in or out of atomic section
              ()
              ()
              (() (atomic)) ; cannot write in or out of atomic section
              )

   ; Atomic fields are accessible without atomic when unique
   (dada-test (cell-ch value hp)
              (test-env (cell-ch (my Cell (ty_my_character))))
              (() (atomic)) ; read in or out of atomic section
              ()
              (() (atomic)) ; write in or out of atomic section
              ()
              )
   (dada-test (cell-ch value hp)
              (test-env (cell-ch (my borrowed () (my Cell (ty_my_character)))))
              (() (atomic)) ; read in or out of atomic section
              ()
              (() (atomic)) ; write in or out of atomic section
              ()
              )

   ; But not if shared
   (dada-test (shvar-cell-ch shv value hp)
              (test-env (shvar-cell-ch (my ShVar ((my Cell (ty_my_character))))))
              ((atomic)) ; read in atomic section
              (()) ; but not out
              ((atomic)) ; write in atomic section
              (()) ; but not out
              )

   ; As above, but test writes directly to the atomic field (which now contains an int)
   (dada-test (shvar-cell-int shv value)
              (test-env (shvar-cell-int (my ShVar ((my Cell (int))))))
              ((atomic)) ; read in atomic section
              (()) ; but not out
              ((atomic)) ; write in atomic section
              (()) ; but not out
              )

   (redex-let* dada-type-system
               [(env_test (term (test-env (shvar-cell-int (my ShVar ((my Cell (int)))))
                                          (pair-ch ty_my_pair_char_str))))]
               (test-judgment-holds (atomic-required-for-read? program_test env_test (shvar-cell-int shv value) (atomic)))
               (test-judgment-holds (atomic-required-for-write? program_test env_test (shvar-cell-int shv value) (atomic)))
               (test-judgment-false (atomic-required-for-read? program_test env_test (shvar-cell-int shv value) ()))
               (test-judgment-false (atomic-required-for-write? program_test env_test (shvar-cell-int shv value) (())))
               (test-judgment-false (atomic-required-for-read? program_test env_test (pair-ch a hp) (atomic)))
               (test-judgment-false (atomic-required-for-write? program_test env_test (pair-ch a hp) (atomic)))
               (test-judgment-holds (atomic-required-for-read? program_test env_test (pair-ch a hp) ()))
               (test-judgment-holds (atomic-required-for-write? program_test env_test (pair-ch a hp) ()))
               )
   )
  )
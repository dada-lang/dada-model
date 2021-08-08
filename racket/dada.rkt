#lang racket
(require redex)
(require "grammar.rkt"
         "opsem.rkt"
         "type-system.rkt"
         "util.rkt")

;; TODO
;;
;; * Generics
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
    (expr-ty
     program
     env_empty
     expr-term
     _
     _)))

 (define-syntax-rule
   (dada-check-exec expr-term value-pattern)
   (begin
     (test-judgment-holds
      (expr-ty
       program
       env_empty
       expr-term
       _
       _))
     (test-match-terms Dada (eval-expr program Store_empty expr-term) (value-pattern _))
     ))

 ;; dada program expected not to type check
 (define-syntax-rule
   (dada-check-fail expr-term)
   (test-judgment-false
    (expr-ty
     program
     env_empty
     expr-term
     _
     _)))

 (dada-check-pass
  ; {
  ;   var pair = ("foo", "bar")
  ;   give pair.a
  ;   give pair.b
  ;   pair.a = "foo1"
  ;   pair.b = "foo2"
  ;   give pair
  ; }
  (seq ((var (pair ty_pair_of_strings) = (class-instance Pair
                                                         (ty_my_string ty_my_string)
                                                         (expr_new_string expr_new_string)))
        (give (pair a))
        (give (pair b))
        (set (pair a) = expr_new_string)
        (set (pair b) = expr_new_string)
        (give (pair)))))

 (dada-check-pass
  ; {
  ;   var pair = ("foo", "bar")
  ;   give pair
  ;   pair.a = "foo1"
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
 
 ; {
 ;   var pair = ("foo", "bar")
 ;   give pair.a
 ;   give pair.b
 ;   pair.a = "foo1"
 ;   // pair.b = "foo2"
 ;   give pair
 ; } // ERROR
 (dada-check-fail
  (seq ((var (pair ty_pair_of_strings) = (class-instance Pair
                                                         (ty_my_string ty_my_string)
                                                         (expr_new_string expr_new_string)))
        (give (pair a))
        (give (pair b))
        (set (pair a) = expr_new_string)
        #;(set (pair b) = expr_new_string)
        (give (pair)))))

 
 (dada-check-fail
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
  ; {
  ;   var pair: shared (String, String) = ("foo", "bar")
  ;   pair.a = "foo1" // ERRO
  ; }
  (seq ((var (pair ty_our_pair_of_strings) = (class-instance Pair
                                                             (ty_my_string ty_my_string)
                                                             (expr_new_string expr_new_string)))
        (set (pair a) = expr_new_string) ; invalidates `pair_a`
        )))

 )
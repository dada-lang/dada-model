#lang racket
(require redex "../grammar.rkt" "../util.rkt")
(require "lang.rkt")
(provide place-is-mutable)

;; place-is-mutable program env place
;;
;; Judgment that determines whether `(set place = ...)` is permitted
;; via the mutability rules. Mutation is permitted under two circumstances:
;;
;; * `place` is a uniquely owned place where each step is `var`
;; * `place` is shared but the fields are atomic (NYI)
(define-judgment-form dada-type-system
  #:mode (place-is-mutable I I I)
  #:contract (place-is-mutable program_in env_in place_in)
  #:inv (all?
         ; the place must be valid in the environment
         (defined? (place-ty program_in env_in place_in)))

  ; Local variables are always mutable
  [--------------------------
   (place-is-mutable _ _ (x))]

  [(can-traverse-to-mutate program env (x f ...))
   (where (my c _) (place-ty program env (x f ...)))
   (where var (class-field-mutability program c f_last))
   --------------------------
   (place-is-mutable program env (x f ... f_last))]

  )

(define-judgment-form dada-type-system
  #:mode (can-traverse-to-mutate I I I)
  #:contract (can-traverse-to-mutate program_in env_in place_in)
  #:inv (all?
         ; the place must be valid in the environment
         (defined? (place-ty program_in env_in place_in)))

  ; Local variables are always mutable
  [--------------------------
   (can-traverse-to-mutate _ _ (x))]

  ; You can traverse through data fields (but not write to them)
  [(where (dt _) (place-ty program env (x f ...)))
   --------------------------
   (can-traverse-to-mutate program env (x f ... f_last))]

  ; Class fields have to be declared mut and also found inside of a
  ; uniquely owned class ("my" type)
  [(where (my c _) (place-ty program env (x f ...)))
   (where var (class-field-mutability program c f_last))
   --------------------------
   (can-traverse-to-mutate program env (x f ... f_last))]

  )

(redex-let*
 dada-type-system
 [(program program_test)
  (ty_my_string (term (my String ())))
  (mode_our (term (shared ())))
  (ty_our_string (term (mode_our String ())))
  (ty_my_pair_of_my_strings (term (my Pair (ty_my_string ty_my_string))))

  ; this is not a "fully normalized" type
  (ty_our_pair_of_my_strings (term (mode_our Pair (ty_my_string ty_my_string))))
  (env (term (test-env (my-pair-o-strings ty_my_pair_of_my_strings)
                       (our-pair-o-strings ty_our_pair_of_my_strings)
                       (my-character (my Character ()))
                       (some-my-pair-o-strings (Some (ty_my_pair_of_my_strings)))
                       (some-my-character (Some ((my Character ())))))))]

 ; can mutate var fields of owned things
 (test-judgment-holds (place-is-mutable program env (my-pair-o-strings a)))

 ; can mutate var fields of owned things reached through data types
 (test-judgment-holds (place-is-mutable program env (some-my-pair-o-strings value a)))

 ; can't mutate fields of shared things
 (test-judgment-false (place-is-mutable program env (our-pair-o-strings a)))

 ; can't mutate shared fields (even of owned things)
 (test-judgment-false (place-is-mutable program env (my-character name))))

#lang racket
(require redex "../grammar.rkt" "../util.rkt" "lang.rkt" "terminate-lease.rkt")
(provide (all-defined-out))

;; definitely-initialized env place -> boolean
;;
;; True if place is definitely initialized
(define-metafunction dada-type-system
  definitely-initialized : env place -> boolean
  [(definitely-initialized env place)
   (place-or-prefix-in place (definitely-initialized-places env))])

;; maybe-initialized env place -> boolean
;;
;; True if place may be initialized
(define-metafunction dada-type-system
  maybe-initialized : env place -> boolean
  [(maybe-initialized env place)
   (place-or-prefix-in place (maybe-initialized-places env))])

;; definitely-not-initialized env place -> boolean
;;
;; True if place is definitely initialized
(define-metafunction dada-type-system
  definitely-not-initialized : env place -> boolean
  [(definitely-not-initialized env place)
   (not (place-or-prefix-in place (maybe-initialized-places env)))])

(redex-let*
 dada-type-system
 [(env (term ((maybe-init ((x) (y f) (y g)))
              (def-init ((x) (y f)))
              (vars ()))))]
 (test-equal (term (definitely-initialized env (x))) #t)
 (test-equal (term (definitely-initialized env (z))) #f)
 (test-equal (term (definitely-initialized env (y f))) #t)
 (test-equal (term (definitely-initialized env (y f f1))) #t)
 (test-equal (term (definitely-initialized env (y g))) #f)
 (test-equal (term (maybe-initialized env (y f g))) #t)
 (test-equal (term (maybe-initialized env (y g h))) #t)
 (test-equal (term (maybe-initialized env (y h))) #f)
 (test-equal (term (definitely-not-initialized env (y h))) #t)
 )

(define-metafunction dada-type-system
  place-extensions : program env place -> places
  [(place-extensions program env place)
   ((x f ... f_place) ...)
   (where ty_place (place-type program env place))
   (where (f_place ...) (field-names program ty_place))
   (where (x f ...) place)
   ]

  )

(redex-let*
 dada-type-system
 [(program program_test)
  (env (term ((maybe-init ((a-point) (a-character)))
              (def-init ((a-point) (a-character)))
              (vars ((a-point (Point ()))
                     (a-character (my Character ()))
                     )))))
  (place_character (term (a-character)))
  ]
 
 (test-equal-terms (place-extensions program env place_character)
                   ((a-character hp) (a-character name) (a-character ac)))

 )
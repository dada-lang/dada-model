#lang racket
(require redex "../grammar.rkt" "../util.rkt" "lang.rkt")
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
   ,(not (term (place-or-prefix-in place (maybe-initialized-places env))))])

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

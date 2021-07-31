#lang racket
(require redex "grammar.rkt" "util.rkt")
(provide (all-defined-out))

(define-extended-language dada-type-system dada
  ;; State of a place P:
  ;;
  ;; * if P or some prefix of P is found in def-init, then definitely initialized
  ;; * if P or some prefix of P is found in maybe-init, then potentially init
  ;; * otherwise, value is known to be uninitialized
  ;;
  ;; If a value is maybe-init, then it is considered live
  ;; (it can still be dropped by a dead comment).
  ;;
  ;; The `(dead x)` command removes `P` from `var-types` and all initialization.
  ;; At runtime, it runs any destructors and cleans up memory. At compilation time,
  ;; it is also used to simulate NLL -- e.g., running `(dead x)` signals that a
  ;; borrow `x` is completed.
  (env ((maybe-init places) (def-init places) (vars var-types)))
  (var-types ((x ty) ...))
  )

(define-metafunction dada-type-system
  maybe-initialized-places : env -> places
  [(maybe-initialized-places ((maybe-init places) _ _)) places])

(define-metafunction dada-type-system
  definitely-initialized-places : env -> places
  [(definitely-initialized-places (_ (def-init places) _)) places])

(define-metafunction dada-type-system
  var-type : env x -> ty
  [(var-type (_ _ (vars var-types))) ,(cadr (assoc (term x) (term var-types)))])

;; subst-ty program generic-decls params ty -> ty
;;
;; Given some `ty` that appeared inside an item
;; with the generics `generic-decls`, substitute the
;; values `params`.
(define-metafunction dada-type-system
  subst-ty : program generic-decls params ty -> ty
  [(subst-ty program () () ty) ty])

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

(let [(env (term ((maybe-init ((x) (y f) (y g)))
                  (def-init ((x) (y f)))
                  (vars ()))))]
  (test-match dada-type-system env env)
  (test-equal (term (definitely-initialized ,env (x))) #t)
  (test-equal (term (definitely-initialized ,env (z))) #f)
  (test-equal (term (definitely-initialized ,env (y f))) #t)
  (test-equal (term (definitely-initialized ,env (y f f1))) #t)
  (test-equal (term (definitely-initialized ,env (y g))) #f)
  (test-equal (term (maybe-initialized ,env (y f g))) #t)
  (test-equal (term (maybe-initialized ,env (y g h))) #t)
  (test-equal (term (maybe-initialized ,env (y h))) #f)
  (test-equal (term (definitely-not-initialized ,env (y h))) #t)
  )

;; merge-leases leases ...
;;
;; Combines some number of leases into one set.
;; The resulting set is in a canonical order, but you
;; cannot in general assume that equivalent sets
;; will be equal. For example:
;;
;; * we don't currently remove leases that are implied by other
;;   other leases (e.g., `(shared (x))` => `(shared (x y))`, but
;;   we will keep both of them.
;; * even if we did, `(shared (x y))` and `(shared (x))`
;;   could be equivalent if `x` has only one field, `y`.
(define-metafunction dada-type-system
  merge-leases : leases ... -> leases

  [(merge-leases leases ...)
   ,(sort (remove-duplicates (append* (term (leases ...)))) place<?)])

;; share-ty program leases ty
;;
;; Transform a type by sharing it.
(define-metafunction dada-type-system
  share-ty : program leases ty -> ty

  ;; "my" class becomes shared
  [(share-ty program leases (my c (param ...)))
   ((shared leases) c params_shared)
   (where (variance ...) (class-variances program c))
   (where params_shared ((share-param program leases variance param) ...))
   ]

  ;; shared classes don't change
  [(share-ty program leases ty)
   ty
   (where ((shared _) c _) ty)]

  ;; data types don't change, but their parameters might
  [(share-ty program leases int)
   int]
  [(share-ty program leases (dt (param ...)))
   (dt params_shared)
   (where (variance ...) (datatype-variances program dt))
   (where params_shared ((share-param program leases variance param) ...))]

  ;; generic types just alter their mode (further changes may result
  ;; after substitution)
  [(share-ty program leases (mode_p p))
   (mode_shared p)
   (where mode_shared (share-mode program leases mode_p))]

  ;; borrowed types
  [(share-ty program leases (mode_b borrowed leases_b ty_b))
   (mode_shared borrowed leases_b ty_b)
   (where mode_shared (share-mode program leases mode_b))]
  )

(define-metafunction dada-type-system
  share-mode : program leases mode -> mode

  [(share-mode program leases my) (shared leases)]
  [(share-mode program leases (shared leases_sh)) (shared leases_sh)])

(define-metafunction dada-type-system
  share-param : program leases variance param -> param

  [(share-param program leases out ty) (share-ty program leases ty)]
  [(share-param program leases _ param) param]
  )

(redex-let*
 dada-type-system
 [(program (term ([(String (class () ()))
                   (Vec (class ((E out)) ()))
                   (Fn (class ((A in) (R out)) ()))
                   (Cell (class ((T inout)) ()))
                   ]
                  [(Point (data () ()))
                   (Option (data ((T out)) ()))
                   ]
                  [])))
  (ty_my_string (term (my String ())))
  (ty_vec_string (term (my Vec (ty_my_string))))
  (ty_option_string (term (Option (ty_my_string))))
  (leases_empty (term ()))
  (ty_shared_string (term ((shared leases_empty) String ())))
  (ty_option_shared_string (term (Option (ty_shared_string))))
  (leases_x (term ((shared (x)))))
  ]

 ;; sharing a class affects mode *and* propagates to out parameters
 (test-equal-terms (share-ty program leases_empty ty_my_string) ty_shared_string)
 (test-equal-terms (share-ty program leases_empty ty_vec_string) ((shared ()) Vec (((shared ()) String ()))))

 ;; sharing a datatype propagates to (out) parameters, but nothing else
 (test-equal-terms (share-ty program leases_empty ty_option_string) ty_option_shared_string)

 ;; sharing something shared: no effect
 (test-equal-terms (share-ty program leases_x ty_shared_string) ty_shared_string)
 )
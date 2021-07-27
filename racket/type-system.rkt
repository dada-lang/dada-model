#lang racket
(require redex)
(require "grammar.rkt")
(provide (all-defined-out))

(define-extended-language dada-type-system dada
  ;; an "access mode" indicates what happens to a value `v` of type `ty`
  ;; after it has been accessed with the mode `my`:
  ;;
  ;; * move -- the old value is invalidated. This occurs if `v` has any
  ;;   uniquely owned things (e.g., `my C`).
  ;; * reborrow -- borrowed things are 'reborrowed' for the next value,
  ;;   which means that the old value cannot be used until the new value
  ;;   is finished. Note that this may also require increasing ref counts
  ;;   for `our` values found within.
  ;; * clone -- increase ref counts for `our` values
  ;; * copy -- no action needed
  (access-mode move reborrow clone copy)

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

;; combine-access-mode: takes the most demanding access mode
(define-metafunction dada-type-system
  combine-access-mode : access-mode access-mode -> access-mode
  [(combine-access-mode access-mode_1 access-mode_2)
   ,(match
        (term (access-mode_1 access-mode_2))
      [(list 'move _) 'move]
      [(list _ 'move) 'move]
      [(list 'reborrow _) 'reborrow]
      [(list _ 'reborrow) 'reborrow]
      [(list 'clone _) 'clone]
      [(list _ 'clone) 'clone]
      [(list 'copy 'copy) 'copy])])

(test-equal (term (combine-access-mode move reborrow)) (term move))
(test-equal (term (combine-access-mode reborrow move)) (term move))
(test-equal (term (combine-access-mode clone move)) (term move))
(test-equal (term (combine-access-mode clone copy)) (term clone))
(test-equal (term (combine-access-mode copy clone)) (term clone))

;; combine-access-modes: given a list of modes, finds the max
(define-metafunction dada-type-system
  combine-access-modes : (access-mode ...) -> access-mode
  [(combine-access-modes ()) copy]
  [(combine-access-modes (access-mode_0 access-mode_1 ...)) (combine-access-mode access-mode_0 (combine-access-modes (access-mode_1 ...)))])


(test-equal (term (combine-access-modes (copy copy clone copy))) (term clone))
(test-equal (term (combine-access-modes (move copy reborrow clone))) (term move))
(test-equal (term (combine-access-modes (copy clone clone move))) (term move))
(test-equal (term (combine-access-modes (copy clone clone reborrow))) (term reborrow))

;; subst-ty program generic-decls params ty -> ty
;;
;; Given some `ty` that appeared inside an item
;; with the generics `generic-decls`, substitute the
;; values `params`.
(define-metafunction dada-type-system
  subst-ty : program generic-decls params ty -> ty
  [(subst-ty program () () ty) ty])

;; ty-access-mode program ty -> access-mode
;;
;; After a value of type `ty` is "moved" with `my`,
;; what operation is needed? This is determined
;; by walking the type recursively to determine what
;; sort of classes are found within.
;;
;; - `move` -- remove the old value
;; - `borrow` -- reborrow existing 
;; - `clone` -- increase ref-counts on `our` classes
;; - `copy` -- just clone (only shared classes or structs)
(define-metafunction dada-type-system
  ty-access-mode : program ty -> access-mode
  [(ty-access-mode program (my c _)) move]
  [(ty-access-mode program (our c _)) clone]
  [(ty-access-mode program ((borrowed _) c _)) reborrow]
  [(ty-access-mode program ((shared _) c _)) copy]
  [(ty-access-mode program int) copy]
  [(ty-access-mode program (s params)) (struct-access-mode program s params (struct-named program s))]
  )

(define-metafunction dada-type-system
  struct-access-mode : program s params struct-definition -> access-mode
  [(struct-access-mode program s params (struct generic-decls ((f ty) ...)))
   (combine-access-modes ((ty-access-mode program (subst-ty program generic-decls params ty)) ...))])

(let [(program
       (term (; classes:
              [
               (some-class (class () []))
               ]
              ; structs:
              [
               (copy-struct (struct () [(f0 int) (f1 int)]))
               (shared-struct (struct () [(f0 ((shared ()) some-class ())) (f1 int)]))
               (clone-struct (struct () [(f0 int) (f1 (our some-class ()))]))
               (borrowed-struct (struct () [(f0 ((borrowed ()) some-class ())) (f1 (our some-class ()))]))
               (move-struct (struct () [(f0 (my some-class ())) (f1 (our some-class ()))]))
               ]
              ; methods:
              []
              )))]
  (test-equal (term (ty-access-mode ,program (copy-struct ()))) (term copy))
  (test-equal (term (ty-access-mode ,program (shared-struct ()))) (term copy))
  (test-equal (term (ty-access-mode ,program (clone-struct ()))) (term clone))
  (test-equal (term (ty-access-mode ,program (borrowed-struct ()))) (term reborrow))
  (test-equal (term (ty-access-mode ,program (move-struct ()))) (term move))
  )

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

;; merge-origins
(define-metafunction dada-type-system
  merge-origins : origins origins -> origins

  [(merge-origins origins_1 origins_2)
   ,(sort (remove-duplicates (append (term origins_1) (term origins_2))) place<?)])

;; merge-mode mode_1 mode_2 -> mode
;;
;; Find find the GLB on the lattice, where a -> b means a >= b
;;
;; my      --->    our
;; |                |
;; v                v
;; borrowed -->  shared
;;
;; The lattice ordering is that mode_1 >= mode_2 if
;;
;;     "having a value in mode_1 gives you more capability
;;      than a value in mode_2"
;;
;; or
;;
;;     "if a program is legal with a value in mode_2,
;;      then it is legal if that value is in mode_1"
;;
;; basically Liskov's substitution principle
;; (i.e., a value in mode_2 <: a value in mode_1).
;;
;;
;; Examples and notes:
;;
;; * `my` is the greatest because you can do anything if you have unique
;;   ownership
;; * `our` and `(borrowed origins)` have no direct ordering because:
;;   - `our` doesn't permit mutating `mut` fields (whereas `borrowed` does)
;;   - but `borrowed origins` doesn't allow creating an `our`, as you lack ownership
;;     - `(borrowed origins)` also forbids access to `origins` (which may be an empty set, though)
;; * `(borrowed origins_1) >= (borrowed origins_2)` if `origins_1 <= origins_2`
;;   - because `(borrowed ())` imposes no restrictions on what you can do with other variables
(define-metafunction dada-type-system
  merge-mode : mode mode -> mode
  [(merge-mode my mode) mode]
  [(merge-mode mode my) mode]
  
  [(merge-mode our our) our]
  [(merge-mode our (shared origins)) (shared origins)]
  [(merge-mode (shared origins) our) (shared origins)]
  [(merge-mode our (borrowed origins)) (shared origins)]
  [(merge-mode (borrowed origins) our) (shared origins)]

  
  [(merge-mode (borrowed origins_1) (borrowed origins_2)) (borrowed (merge-origins origins_1 origins_2))]
  [(merge-mode (borrowed origins_1) (shared origins_2)) (shared (merge-origins origins_1 origins_2))]
  [(merge-mode (shared origins_1) (borrowed origins_2)) (shared (merge-origins origins_1 origins_2))]

  [(merge-mode (shared origins_1) (shared origins_2)) (shared (merge-origins origins_1 origins_2))]
  )

;; apply-mode program mode ty
;;
;; Applying a mode to a type means converting to the 'least mode'
;; of the mode in the type already. So e.g. a "shared" version of
;; a "borrowed" class is a "shared class".
(define-metafunction dada-type-system
  apply-mode-to-ty : program mode ty -> ty
  [(apply-mode-to-ty _ _ int) int]
  [(apply-mode-to-ty program mode (s params))
   (s params_out)
   (where variances (struct-variances program s))
   (where (params_out origins_out) (apply-mode-to-programs program mode variances params))]
  [(apply-mode-to-ty program mode_1 (mode_c c params))
   (mode_out c params_out)
   (where mode_out (merge-mode mode_1 mode_c))
   (where variances (class-variances program c))
   (where params_out (apply-mode-to-params program mode_out variances params))]
  )

(define-metafunction dada-type-system
  apply-mode-to-params : program mode variances params -> params
  [(apply-mode-to-params program mode (variance ...) (param ...))
   (param_out ...)
   (where (param_out ...) ((apply-mode-to-param program mode variance param) ...))
  ])

(define-metafunction dada-type-system
  apply-mode-to-param : program mode variance param -> param

  ;; Perhaps surprisingly, applying a mode to a "in" (contravariant) parameter
  ;; has no effect. Consider: if I have a function that expects T and I share it,
  ;; the function still expects a T. (Not a shared T.)
  [(apply-mode-to-param _ _ in param) param]
  [(apply-mode-to-param _ _ inout param) param]
  
  ;; In contrast, if I have a vector of T and I share it, I now have only shared
  ;; access to the T within.
  [(apply-mode-to-param program mode out ty) (apply-mode-to-ty program mode ty)]
  [(apply-mode-to-param program mode out origins) (apply-mode-to-origins program mode origins)]
  )

(define-metafunction dada-type-system
  apply-mode-to-origins : program mode origins -> origins
  [(apply-mode-to-origins _ my origins) origins]
  [(apply-mode-to-origins _ our origins) origins]

  ;; Given `struct Foo<origins o> { shared(o) String }`
  ;; then `shared(o1) Foo<o2>` means that the origins for
  ;; my String are `(o1, o2)`.
  ;;
  ;; Wait-- is that reasonable? Answer: no. FIXME
  [(apply-mode-to-origins _ (borrowed origins_b) origins) (merge-origins origins_b origins)]
  [(apply-mode-to-origins _ (shared origins_b) origins) (merge-origins origins_b origins)]
  )

(let [(program
       (term (; classes:
              [(the-class (class () ()))]
              ; structs:
              []
              ; methods:
              []
              )))]
  (test-equal (term (merge-origins ((shared (x)) (shared (z))) ((shared (y))))) (term ((shared (x)) (shared (y)) (shared (z)))))

  ;; we could actually do better here, because `(shared x)` subsumes `(shared (x y))`
  (test-equal (term (merge-origins ((shared (x)) (shared (z))) ((shared (z)) (shared (x y))))) (term ((shared (x)) (shared (x y)) (shared (z)))))

  ;; we could actually do better here, because `(shared x)` subsumes `(borrowed x)`
  (test-equal (term (merge-origins ((shared (x))) ((borrowed (x))))) (term ((borrowed (x)) (shared (x)))))

  (test-equal (term (apply-mode-to-ty ,program (shared ((shared (x)))) (my the-class ()))) (term ((shared ((shared (x)))) the-class ())))

  ;; Here: it's important that origins carry an origin-kind,
  ;; because we have to remember that the shared reference came from a
  ;; `borrowed (y)`!
  (test-equal (term (apply-mode-to-ty ,program (shared ((shared (x)))) ((borrowed ((borrowed (y)))) the-class ()))) (term ((shared ((borrowed (y)) (shared (x)))) the-class ())))
  )
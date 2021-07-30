#lang racket
(require redex "grammar.rkt" "util.rkt")
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
               (move-struct (struct () [(f0 (my some-class ())) (f1 (our some-class ()))]))
               ]
              ; methods:
              []
              )))]
  (test-equal (term (ty-access-mode ,program (copy-struct ()))) (term copy))
  (test-equal (term (ty-access-mode ,program (shared-struct ()))) (term copy))
  (test-equal (term (ty-access-mode ,program (clone-struct ()))) (term clone))
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

;; leases-in-ty ty
;;
;; Returns the set of leases (unioned) that appear in the type `ty`.
;; Note that if `ty` includes generic parameters, the full set of leases
;; may not be known (though this is rarely relevant).
;;
;; Note that this function does not take a `program`. This is by design:
;; knowledge of which leases may appear in a type ought to be visible
;; purely from the type itself, without descending into definitions.
(define-metafunction dada-type-system
  leases-in-ty : ty -> leases
  [(leases-in-ty int) ()]
  [(leases-in-ty (mode p)) (leases-in-mode mode)]
  [(leases-in-ty (s params)) (leases-in-params params)]
  [(leases-in-ty (mode c params)) (merge-leases (leases-in-mode mode) (leases-in-params params))]
  )

;; leases-in-mode
;;
;; Leases appearing in mode.
(define-metafunction dada-type-system
  leases-in-mode : mode -> leases

  [(leases-in-mode my) ()]
  [(leases-in-mode our) ()]
  [(leases-in-mode (shared leases)) leases])

;; leases-in-params
;;
;; Leases appearing in lits of parameters.
(define-metafunction dada-type-system
  leases-in-params : params -> leases

  [(leases-in-params (param ...)) (merge-leases (leases-in-param param) ...)])

;; leases-in-param
;;
;; Leases appearing in lits of parameters.
(define-metafunction dada-type-system
  leases-in-param : param -> leases

  [(leases-in-param ty) (leases-in-ty ty)]
  [(leases-in-param lease) (lease)])

;; add-leases-to-mode mode leases
;;
;; If the mode `mode` is not an owned mode,
;; include `leases` in it.
(define-metafunction dada-type-system
  add-leases-to-mode : mode leases -> mode

  [(add-leases-to-mode my _) my]
  [(add-leases-to-mode our _) our]
  [(add-leases-to-mode (shared leases_m) leases) (shared (merge-leases leases_m leases))]
  )

;; merge-mode mode_1 mode_2 -> mode
;;
;; Find the GLB on the lattice, where a -> b means a >= b
;;
;; my ---> our ---> shared
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
(define-metafunction dada-type-system
  merge-mode : mode mode -> mode
  [(merge-mode my mode) mode]
  [(merge-mode mode my) mode]
  
  [(merge-mode our our) our]
  [(merge-mode our (shared leases)) (shared leases)]
  [(merge-mode (shared leases) our) (shared leases)]
  
  [(merge-mode (shared leases_1) (shared leases_2)) (shared (merge-leases leases_1 leases_2))]
  )

;; apply-mode program mode ty
;;
;; Applying a mode to a type means converting to the 'least mode'
;; of the mode in the type already. So e.g. a "shared" version of
;; a "my" class is a "shared class".
(define-metafunction dada-type-system
  apply-mode-to-ty : program mode ty -> ty
  [(apply-mode-to-ty _ _ int) int]
  [(apply-mode-to-ty program mode (s params))
   (s params_out)
   (where variances (struct-variances program s))
   (where params_out (apply-mode-to-params program mode variances params))
   ]
  [(apply-mode-to-ty program mode_1 (mode_c c params))
   (mode_out c params_out)
   (where mode_merged (apply-mode-to-mode program mode_1 mode_c))
   (where mode_out (add-leases-to-mode mode_merged (leases-in-params params)))
   (where variances (class-variances program c))
   (where params_out (apply-mode-to-params program mode_out variances params))
   ]
  )

(define-metafunction dada-type-system
  apply-mode-to-params : program mode variances params -> params
  [(apply-mode-to-params program mode (variance ...) (param ...))
   ((apply-mode-to-param program mode variance param) ...)
   ])

;; "Apply mode to param" is a sort of heuristic that normalizes
;; generic parameters within types when they are shared. For structs,
;; it is necessary, since they don't carry a mode of their own.
;; For classes, it could be replaced with an identity function without
;; causing unsoundness, but it allows more programs to type check and
;; makes working with data easier.
;;
;; Intuitively, what happens here is that you have a `my Vec<my String>`
;; (say) and you share it. Without this function, you might get a `shared(o) Vec<my String>`
;; but with this function, you get a `shared(o) Vec<shared(o) String>`.
;; This reflects the fact that if you have a shared vector, you can only get
;; shared things out.
;;
;; The reason that we say the function is "optional" is that when you access
;; a field of a class, its type is always adjusted based on the mode of the
;; receiver. This is necessary because it is not always sound to transform a
;; parameter based on the mode. For example, type parameters used in `atomic`
;; fields are invariant; similarly, lease parameters could be used in multiple
;; ways so we don't know how to transform them. In this case, the transformation
;; is done when the actual field is used.
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

  ;; Leases can be used in `shared(o)` expressions, so 
  [(apply-mode-to-param program mode out leases) leases]
  )

(define-metafunction dada-type-system
  apply-mode-to-mode : program mode mode -> mode
  ;; joint modes don't change
  [(apply-mode-to-mode _ _ our) our]
  [(apply-mode-to-mode _ _ (shared leases)) (shared leases)]

  ;; taking unique ownership of something never changes its mode
  [(apply-mode-to-mode _ my mode) mode]

  ;; taking joint ownership of something means it is no longer unique
  [(apply-mode-to-mode _ our my) our]

  ;; sharing something means it is no longer unique
  [(apply-mode-to-mode _ (shared leases_1) my) (shared leases_1)]
  )

(let [(program
       (term (; classes:
              [
               (the-class (class () ()))
               (vec (class ((Element out)) ()))
               (cell (class ((Element inout)) ()))
               (guard (class ((Element out)) ()))
               ]
              ; structs:
              [
               (option (struct ((Element out)) ()))
               ]
              ; methods:
              []
              )))]
  (test-equal (term (merge-leases ((shared (x)) (shared (z))) ((shared (y))))) (term ((shared (x)) (shared (y)) (shared (z)))))

  ;; we could actually do better here, because `(shared x)` subsumes `(shared (x y))`
  (test-equal (term (merge-leases ((shared (x)) (shared (z))) ((shared (z)) (shared (x y))))) (term ((shared (x)) (shared (x y)) (shared (z)))))

  (test-match dada-type-system ty (term (option ((my the-class ())))))
  (test-match dada-type-system mode (term (shared ((shared (x))))))
  (test-match dada-type-system program program)
  (test-equal-terms (apply-mode-to-ty ,program (shared ((shared (x)))) (option ((my the-class ()))))
                    (option (((shared ((shared (x)))) the-class ()))))

  (test-equal-terms (apply-mode-to-ty ,program
                                      (shared ((shared (x))))
                                      (option ((our the-class ()))))
                    (option ((our the-class ()))))

  (test-equal (term (apply-mode-to-ty ,program (shared ((shared (x)))) (my the-class ()))) (term ((shared ((shared (x)))) the-class ())))

  )
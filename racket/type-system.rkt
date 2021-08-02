#lang racket
(require redex "grammar.rkt" "util.rkt")
(require "type-system/lang.rkt" "type-system/initialization.rkt" "type-system/terminate-lease.rkt")
(provide (all-defined-out)
         (all-from-out "type-system/lang.rkt")
         (all-from-out "type-system/initialization.rkt")
         (all-from-out "type-system/terminate-lease.rkt"))

;; expr-type env_in expr_in ty_out env_out
;;
;; Computes the type of an expression in a given environment,
;; as well as the resulting environment for subsequent expressions.
(define-judgment-form
  dada-type-system
  #:mode (expr-type I I I O O)
  #:contract (expr-type program env expr ty env)

  ;; Numbers always have type `int`.
  [--------------------------
   (expr-type _ env_in number int env_in)]

  ;; Empty sequences have int type.
  [--------------------------
   (expr-type _ env_in (seq) int env_in)]

  ;; Sequences thread the environment through each expr,
  ;; and they discard intermediate values. Their type is
  ;; the type of the final value.
  [(expr-type program env_in (seq expr_0 ...) ty_mid env_mid)
   (expr-type program env_mid expr_last ty_last env_last)
   --------------------------
   (expr-type program env_in (seq expr_0 ... expr_last) ty_last env_last)]

  ;; Sharing a place:
  ;;
  ;; * Sharing qualifies as a read.
  ;; * The data must be "definitely-initialized".
  ;; * If we are sharing something that is already shared,
  ;;   then the resulting type doesn't change, and hence
  ;;   the reusting value is independent of `place`.
  ;; * But if we are sharing something owned, then we
  ;;   get back a `(shared place)` lease.
  [(side-condition (definitely-initialized env_in place))
   (where leases ((shared place)))
   (where ty_place (place-ty program env_in place))
   (where ty_shared (share-ty program leases ty_place))
   (where env_out (terminate-lease program env_in read place))
   --------------------------
   (expr-type program env_in (share place) ty_shared env_out)]

  )

(redex-let*
 dada-type-system
 [(program (term ([(String (class () ()))
                   (Pair (class ((A out) (B out)) ((a (my A)) (b (my B)))))
                   (Vec (class ((E out)) ()))
                   (Fn (class ((A in) (R out)) ()))
                   (Cell (class ((T inout)) ()))
                   ]
                  [(Point (data () ()))
                   (Option (data ((T out)) ()))
                   ]
                  [])))
  (ty_my_string (term (my String ())))
  (ty_sh_string (term ((shared ((shared (the-string)))) String ())))
  (env_sh (term ((maybe-init ((the-string) (sh-string)))
                 (def-init ((the-string) (sh-string)))
                 (vars (
                        (the-string ty_my_string)
                        (sh-string ty_sh_string)
                        )))))

  (ty_my_pair (term (my Pair (ty_my_string ty_sh_string))))
  (ty_sh_from_pair_string (term ((shared  ((shared (pair)))) String ())))
  (env_pair (term ((maybe-init ((the-string) (pair) (from-pair)))
                   (def-init ((the-string) (pair) (from-pair)))
                   (vars (
                          (the-string ty_my_string)
                          (pair ty_my_pair)
                          (from-pair ty_sh_from_pair_string)
                          )))))

  (ty_b_string (term (my borrowed ((borrowed (the-string))) ty_my_string)))
  (env_b (term ((maybe-init ((the-string) (b-string)))
                (def-init ((the-string) (b-string)))
                (vars (
                       (the-string ty_my_string)
                       (b-string ty_b_string)
                       )))))

  (lease_x (term (shared (the-string))))
  (action_x (term (read (the-string))))
  ]

 (test-equal-terms lease_x lease_x)
 )
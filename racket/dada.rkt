;; Main dada export:
;;
;; Exports the reduction, type system, and various macros to run
;; tests. This is imported by the tests in z-tests but also
;; by dada-debug, so that we can copy and paste an individual
;; test to debug in isolation.

#lang racket
(require redex/reduction-semantics rackunit sexp-diff)
(require "grammar.rkt"
         "opsem.rkt"
         "type-system.rkt"
         "util.rkt"
         "opsem/lease.rkt"
         "opsem/heap.rkt"
         "opsem/lang.rkt"
         "opsem/stack.rkt"
         "opsem/test-store.rkt"
         "opsem/traverse.rkt"
         )
(provide dada-check-pass
         dada-check-fail
         dada-check-exec
         dada-check-program-ok
         dada-check-program-not-ok
         dada-let-store
         dada-seq-test
         dada-full-test
         dada-trace-test
         dada-pretty-print
         dada-test-share
         dada-test-give
         dada-test-lend
         program_test
         program-with-methods
         Dada
         Dada-reduction
         test-program
         the-Zero-value
         test-store
         )

(define-syntax-rule
  ;; dada-check-program-ok
  ;;
  ;; Checks that a program type checks successfully.
  (dada-check-program-ok program-term)
  (test-judgment-holds (program-ok program-term)))

(define-syntax-rule
  ;; dada-check-program-not-ok
  ;;
  ;; Checks that a program type checks successfully.
  (dada-check-program-not-ok program-term)
  (test-judgment-false (program-ok program-term)))

(define-syntax-rule
  ;; dada-check-pass
  ;;
  ;; Checks that a program type checks successfully.
  (dada-check-pass program-term expr-term)
  (test-judgment-holds
   (expr-drop
    program-term
    env_empty
    expr-term
    _)))

(define-syntax-rule
  ;; dada-pretty-print
  ;;
  ;; Pretty prints the resulting type and environment. Useful for debugging.
  (dada-pretty-print program-term expr-term)
  (pretty-print
   (judgment-holds
    (expr-ty
     program-term
     env_empty
     expr-term
     ty_out
     env_out)
    (ty_out env_out))))

(define-syntax-rule
  ;; dada-check-exec
  ;;
  ;; Checks that a program type-checks and that it evaluates
  ;; to a value matching the given pattern.
  (dada-check-exec program-term expr-term value-pattern)
  (begin
    (test-judgment-holds
     (expr-drop
      program-term
      env_empty
      expr-term
      _))
    (test-match-terms Dada (eval-expr ,program_test Store_empty expr-term) (value-pattern _))
    ))

(define-syntax-rule
  ;; dada-check-fail
  ;;
  ;; check that a program fails to type check.
  (dada-check-fail program-term expr-term)
  (test-judgment-false
   (expr-drop
    program-term
    env_empty
    expr-term
    _)))

(define-syntax-rule
  ;; dada-seq-test
  ;;
  ;; Embed the list of expr in a (seq) block and execute them.
  ;;
  ;; Check the state of the program *just before* the seq block is
  ;; popped.
  ;;
  ;; Useful for inspecting the types of variables and state of the heap.
  (dada-seq-test [expr ...] [var ...] [heap ...] [lease ...] value)

  (redex-let*
   Dada
   [(Store_out (term (store-with-lease-mappings
                      (store-with-heap-entries
                       (store-with-vars (push-stack-segment Store_empty) var ...)
                       heap ...)
                      (lease ...))))
    (Config_start (term (program_test Store_empty (seq (expr ...)))))
    (any_expected (term ((program_test Store_out (seq-pushed (value))))))
    (any_actual (apply-reduction-relation* Dada-reduction
                                           (term Config_start)
                                           #:stop-when outer-seq-complete?))

    ]

   #;(pretty-print (term Config_start))
   #;(pretty-print (term any_actual))
   #;(pretty-print (term any_expected))
   (when (not (equal? (term any_actual) (term any_expected)))
     (pretty-print (sexp-diff (term any_expected)
                              (term any_actual)
                              #:old-marker '#:expected
                              #:new-marker '#:actual)))
   (check-equal? (term any_actual) (term any_expected) (term (expr ...)))))

(define-syntax-rule
  ;; dada-let-store
  ;;
  ;; Execute a set of expressions and extract the final Store, binding
  ;; it to the given name in term.
  (dada-let-store ((Store-name = [expr ...]) var ...) body ...)

  (redex-let*
   Dada
   [(Config_start (term (program_test Store_empty (seq (expr ...)))))
    (((_ Store-name (seq-pushed (_)))) (apply-reduction-relation* Dada-reduction
                                                                  (term Config_start)
                                                                  #:stop-when outer-seq-complete?))
    var ...

    ]
   body ...
   )
  )

(define-syntax-rule
  ;; dada-trace-test
  ;;
  ;; Same form as dada-seq-test, but dumps out the tracing output.
  ;; Useful for debugging.
  (dada-trace-test [expr ...] other ...)
  (traces Dada-reduction (term (program_test Store_empty (seq (expr ...))))))

(define-syntax-rule
  ;; dada-full-test
  ;;
  ;; Fully execute the given expressions and check the final value that we compute.
  ;; Note that it is assumed there will be nothing on the stack.
  (dada-full-test [expr ...] [heap ...] [lease ...] value)

  (redex-let*
   Dada
   [(Store_out (term (store-with-lease-mappings
                      (store-with-heap-entries
                       Store_empty
                       heap ...)
                      (lease ...))))
    (Config_start (term (program_test Store_empty (seq (expr ...)))))
    (any_expected (term ((program_test Store_out value))))
    (any_actual (apply-reduction-relation* Dada-reduction
                                           (term Config_start)))

    ]

   #;(pretty-print (term Config_start))
   #;(pretty-print (term any_actual))
   #;(pretty-print (term any_expected))
   (when (not (equal? (term any_actual) (term any_expected)))
     (pretty-print (sexp-diff (term any_expected)
                              (term any_actual)
                              #:old-marker '#:expected
                              #:new-marker '#:actual)))
   (check-equal? (term any_actual) (term any_expected) (term (expr ...)))))

(define-syntax-rule
  (dada-test-share inner-perm outer-perm field-perm result perm-sh-term (lease-id lease-kind-term lease-parents) ...)
  ;; See opsem-access-patterns: generates a program that contains one value embedded in another with
  ;; different modes. Tests the result of `dada-access-term` and the result of of sharing that
  ;; value.

  (dada-let-store
   ((Store = ((var inner = (class-instance String () ()))
              (var outer = (class-instance (dada-class-name field-perm) () ((dada-access-term inner-perm inner))))
              (var outer-access = (dada-access-term outer-perm outer))
              (var s = (share (outer-access value)))
              ))
    (Traversal_0 (term (traversal program_test Store (outer-access value))))
    ((Permission_sh box Address_sh) (term (var-in-store Store s)))
    )
   (; otherwise we get no line numbers etc
    pretty-print (term ("share" inner-perm outer-perm field-perm)))
   (test-equal-terms (access-permissions Traversal_0)
                     result)
   (test-equal-terms Permission_sh
                     perm-sh-term)
   (redex-let*
    Dada
    [((Lease-kind_l Leases_l Address_l) (term (lease-data-in-store Store lease-id)))]
    (test-equal-terms Lease-kind_l lease-kind-term)
    (test-equal-terms Leases_l lease-parents)
    ) ...
      )

  )

(define-metafunction Dada
  dada-access-term : Permission x -> expr
  ;; Generates an expression that accesses `x` with the given permission.

  [(dada-access-term my x) (give (x))]
  [(dada-access-term our x) (share (give (x)))]
  [(dada-access-term (shared _) x) (share (x))]
  [(dada-access-term (lent _) x) (lend (x))]
  )

(define-metafunction Dada
  dada-class-name : mutability -> c
  ;; Generates a class name whose `value` field has the given mutability.

  [(dada-class-name var) Some]
  [(dada-class-name shared) Shared]
  [(dada-class-name atomic) Cell]
  )

(define-syntax-rule
  (dada-test-give inner-perm outer-perm field-perm perm-give-term old-value-term (lease-id lease-kind-term lease-parents) ...)
  ;; See opsem-access-patterns: generates a program that contains one value embedded in another with
  ;; different modes. Tests the result of giving that inner value.

  (begin
    (; otherwise we get no line numbers etc
     pretty-print (term ("give" inner-perm outer-perm field-perm)))
    (dada-let-store
     ((Store = ((var inner = (class-instance String () ()))
                (var outer = (class-instance (dada-class-name field-perm) () ((dada-access-term inner-perm inner))))
                (var outer-access = (dada-access-term outer-perm outer))
                (var g = (give (outer-access value)))
                ))
      ((Permission_sh box Address_sh) (term (var-in-store Store g)))
      ((_ ((value Value_old))) (term (load-heap Store Heap-addr1)))
      )

     (test-equal-terms Permission_sh
                       perm-give-term)
     (test-match Dada old-value-term (term Value_old))
     (redex-let*
      Dada
      [((Lease-kind_l Leases_l Address_l) (term (lease-data-in-store Store lease-id)))]
      (test-equal-terms Lease-kind_l lease-kind-term)
      (test-equal-terms Leases_l lease-parents)
      ) ...)))

(define-syntax-rule
  (dada-test-lend inner-perm outer-perm field-perm perm-lend-term (lease-id lease-kind-term lease-parents) ...)
  ;; See opsem-access-patterns: generates a program that contains one value embedded in another with
  ;; different modes. Tests the result of giving that inner value.

  (begin
    (; otherwise we get no line numbers etc
     pretty-print (term ("lend" inner-perm outer-perm field-perm)))
    (dada-let-store
     ((Store = ((var inner = (class-instance String () ()))
                (var outer = (class-instance (dada-class-name field-perm) () ((dada-access-term inner-perm inner))))
                (var outer-access = (dada-access-term outer-perm outer))
                (var l = (lend (outer-access value)))
                ))
      ((Permission_sh box Address_sh) (term (var-in-store Store l)))
      )

     (test-equal-terms Permission_sh
                       perm-lend-term)
     (redex-let*
      Dada
      [((Lease-kind_l Leases_l Address_l) (term (lease-data-in-store Store lease-id)))]
      (test-equal-terms Lease-kind_l lease-kind-term)
      (test-equal-terms Leases_l lease-parents)
      ) ...)))
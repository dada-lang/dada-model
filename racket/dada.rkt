#lang racket
(require redex)
(require "grammar.rkt"
         "opsem.rkt"
         "type-system.rkt"
         "util.rkt"
         "opsem/lease.rkt"
         "opsem/heap.rkt"
         "opsem/lang.rkt"
         "opsem/stack.rkt")
(provide dada-check-pass
         dada-check-fail
         dada-check-exec
         dada-check-program-ok
         dada-check-program-not-ok
         dada-seq-test
         dada-full-test
         dada-trace-test
         dada-pretty-print
         program_test
         program-with-methods
         Dada
         Dada-reduction
         test-program
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
                      (lease ...))))]
   #;(pretty-print (term (program_test Store_empty (seq (expr ...)))))
   (test-->>E Dada-reduction
              (term (program_test Store_empty (seq (expr ...))))
              (term (program_test Store_out (seq-pushed (value)))))))

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
                      (lease ...))))]
   (test-->> Dada-reduction
             (term (program_test Store_empty (seq (expr ...))))
             (term (program_test Store_out value)))))




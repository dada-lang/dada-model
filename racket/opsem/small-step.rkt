#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         "../grammar.rkt"
         "../type-system.rkt"
         "../util.rkt"
         "lang.rkt"
         "drop.rkt"
         "read-write.rkt"
         "clone.rkt"
         "heap.rkt"
         "stack.rkt"
         "lease.rkt")
(provide Dada-reduction)

(define Dada-reduction
  (reduction-relation
   Dada

   (; Special case: empty sequences evaluate to 0.
    --> (program Store (in-hole Expr (seq ())))
        (program Store (in-hole Expr 0)))

   (; Before a sequence starts executing, we need to push a fresh
    ; stack segment.
    --> (program Store (in-hole Expr (seq (expr_0 expr_1 ...))))
        (program (push-stack-segment Store) (in-hole Expr (seq-pushed (expr_0 expr_1 ...)))))

   (; Sequences evaluate to the value of the final expression
    --> (program Store (in-hole Expr (seq-pushed (Value))))
        (program Store_dropped (in-hole Expr Value))
        (where/error (Values_popped Store_popped) (pop-stack-segment Store))
        (where/error Store_dropped (drop-values Store_popped Values_popped)))

   (; Sequences drop intermediate values
    --> (program Store (in-hole Expr (seq-pushed (Value expr_0 expr_1 ...))))
        (program Store_out (in-hole Expr (seq-pushed (expr_0 expr_1 ...))))
        (where/error Store_out (drop-value Store Value)))

   (; var x = Value
    --> (program Store (in-hole Expr (var x = Value)))
        (program Store_out (in-hole Expr 0))
        (where/error Store_out (store-with-var Store x Value)))

   (; set place-at-rest = Value
    --> (program Store (in-hole Expr (set place-at-rest = Value)))
        (program Store_out (in-hole Expr 0))
        (where/error (Value_old _ Store_read) (read-place Store place-at-rest))
        (where/error Store_write (write-place Store_read place-at-rest Value))
        (where/error Store_out (drop-value Store_write Value_old)))

   (; move place
    --> (program Store (in-hole Expr (move place)))
        (program Store_out (in-hole Expr Value))
        (where/error (Value Store_out) (move-place Store place)))

   (; give place
    --> (program Store (in-hole Expr (give place)))
        (program Store_out (in-hole Expr Value))
        (where/error (Value _ Store_read) (read-place Store place))
        (where/error Store_out (write-place Store_read place expired)))

   (; copy place
    --> (program Store (in-hole Expr (copy place)))
        (program Store_out (in-hole Expr Value))
        (where/error (Value _ Store_read) (read-place Store place))
        (where/error Store_out (clone-value Store_read Value)))

   (; share place
    --> (program Store (in-hole Expr (share place)))
        (program Store_out (in-hole Expr Value))
        (where/error (Value Store_out) (share-place Store place)))

   (; lend place
    --> (program Store (in-hole Expr (lend place)))
        (program Store_out (in-hole Expr Value))
        (where/error (Value Store_out) (lend-place Store place)))

   (; class-instance c params Value
    --> (program Store (in-hole Expr (class-instance c params (Value ...))))
        (program Store_out (in-hole Expr Value_out))
        (where/error (f_c ...) (class-field-names program c))
        (where/error (Value_out Store_out) (allocate-box-in-store Store ((class c) ((f_c Value) ...)))))

   (; atomic Value
    ;
    ; Since we're not modeling threads, nothing to do here.
    --> (program Store (in-hole Expr (atomic Value)))
        (program Store (in-hole Expr Value)))

   (; Value upcast
    ;
    ; No-op at runtime.
    --> (program Store (in-hole Expr (Value : ty)))
        (program Store (in-hole Expr Value)))

   (; assert-ty
    ;
    ; Just accesses the place.
    --> (program Store (in-hole Expr (assert-ty place-at-rest : ty)))
        (program Store (in-hole Expr 0))
        (where _ (read-place Store place-at-rest)))

   ))

(module+ test
  ; a few *very* simple tests. most of the tests live in the integration-tests directory.
  (test-->> Dada-reduction
            (term (program_test Store_empty (seq ())))
            (term (program_test Store_empty 0)))

  (test-->> Dada-reduction
            (term (program_test Store_empty (var my-var = 22)))
            (term (program_test (store-with-vars Store_empty (my-var 22)) 0)))
  )
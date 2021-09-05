#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         "../grammar.rkt"
         "../type-system.rkt"
         "../util.rkt"
         "lang.rkt"
         "drop.rkt")
(provide Dada-reduction)

(define Dada-reduction
  (reduction-relation
   Dada

   #;(; Integers evaluate to themselves.
      --> (program Store (in-hole Expr number))
          (program Store (in-hole Expr (number : int))))

   (; Empty sequences evaluate to 0.
    --> (program Store (in-hole Expr (seq ())))
        (program Store (in-hole Expr 0)))

   (; Sequences evaluate to the value of the final expression
    --> (program Store (in-hole Expr (seq (Value))))
        (program Store (in-hole Expr Value)))

   (; Sequences drop intermediate values
    --> (program Store (in-hole Expr (seq (Value expr_0 expr_1 ...))))
        (program Store_out (in-hole Expr (seq (expr_0 expr_1 ...))))
        (where/error Store_out (drop-value Store Value)))

   (; var x = Value-ty
    --> (program Store (in-hole Expr (var x = Value)))
        (program Store_out (in-hole Expr 0))
        (where/error Store_out (store-with-stack-mapping Store (x Value))))
   
   #;(; give place
    --> (program Store (in-hole Expr (give place)))
        (program Store_out (in-hole Expr Value))
        (where/error Value (read Store place))
        (where/error Store_out (write Store place expired)))
   
   ))

(module+ test
  (test-->> Dada-reduction
            (term (program_test Store_empty (seq ())))
            (term (program_test Store_empty 0)))
  (test-->> Dada-reduction
            (term (program_test Store_empty (var my-var = 22)))
            (term (program_test (store-with-stack-mapping Store_empty (my-var 22)) 0)))
  (test-->> Dada-reduction
            (term (program_test Store_empty (seq ((var my-var = 22) (var another-var = 44)))))
            (term (program_test (store-with-stack-mappings Store_empty (my-var 22) (another-var 44)) 0)))
  
  )
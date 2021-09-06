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
         "heap.rkt")
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

   (; var x = Value
    --> (program Store (in-hole Expr (var x = Value)))
        (program Store_out (in-hole Expr 0))
        (where/error Store_out (store-with-stack-mapping Store (x Value))))

   (; set place-at-rest = Value
    --> (program Store (in-hole Expr (set place-at-rest = Value)))
        (program Store_out (in-hole Expr 0))
        (where/error Value_old (read-place Store place-at-rest))
        (where/error Store_write (write-place Store place-at-rest Value))
        (where/error Store_out (drop-value Store_write Value_old)))
   
   (; give place
    --> (program Store (in-hole Expr (give place)))
        (program Store_out (in-hole Expr Value))
        (where/error Value (read-place Store place))
        (where/error Store_out (write-place Store place expired)))

   (; copy place
    --> (program Store (in-hole Expr (copy place)))
        (program Store_out (in-hole Expr Value))
        (where/error Value (read-place Store place))
        (where/error Store_out (clone-value Store Value)))

   (; share place
    --> (program Store (in-hole Expr (share place)))
        (program Store_out (in-hole Expr Value))
        (where/error (Value Store_out) (share-place Store place)))

   (; data-instance dt params Value
    --> (program Store (in-hole Expr (data-instance dt params (Value ...))))
        (program Store_out (in-hole Expr Value_out))
        (where/error (f_c ...) (datatype-field-names program dt))
        (where/error (Value_out Store_out) (allocate-box-in-store Store ((data dt) ((f_c Value) ...)))))

   (; class-instance dt params Value
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
  (test-->> Dada-reduction
            (term (program_test Store_empty (seq ())))
            (term (program_test Store_empty 0)))
  
  (test-->> Dada-reduction
            (term (program_test Store_empty (var my-var = 22)))
            (term (program_test (store-with-stack-mapping Store_empty (my-var 22)) 0)))
  
  (test-->> Dada-reduction
            (term (program_test Store_empty (seq ((var my-var = 22) (var another-var = 44)))))
            (term (program_test (store-with-stack-mappings Store_empty (my-var 22) (another-var 44)) 0)))

  (test-->> Dada-reduction
            (term (program_test Store_empty (seq ((var my-var = 22) (var another-var = 44) (give (another-var))))))
            (term (program_test (store-with-stack-mappings Store_empty (my-var 22) (another-var expired)) 44)))

  (test-->> Dada-reduction
            (term (program_test Store_empty (seq ((var my-var = 22) (var another-var = 44) (copy (another-var))))))
            (term (program_test (store-with-stack-mappings Store_empty (my-var 22) (another-var 44)) 44)))

  (test-->> Dada-reduction
            (term (program_test Store_empty (seq ((var my-var = 22) (var another-var = (44 : int)) (copy (another-var))))))
            (term (program_test (store-with-stack-mappings Store_empty (my-var 22) (another-var 44)) 44)))

  (; Test creating a data instance and copying it.
   ; The ref count winds up as 2.
   test-->> Dada-reduction
            (term (program_test Store_empty (seq ((var my-var = 22)
                                                  (var point = (data-instance Point () (22 33)))
                                                  (copy (point))
                                                  ))))
            (term (program_test
                   [[(point (my box Heap-addr)) (my-var 22)]
                    [(Heap-addr (box 2 ((data Point) ((x 22) (y 33)))))]]
                   (my box Heap-addr))))

  (; Test creating a data instance and giving it.
   ; The ref count winds up as 1.
   test-->> Dada-reduction
            (term (program_test Store_empty (seq ((var my-var = 22)
                                                  (var point = (data-instance Point () (22 33)))
                                                  (give (point))
                                                  ))))
            (term (program_test
                   [[(point expired) (my-var 22)]
                    [(Heap-addr (box 1 ((data Point) ((x 22) (y 33)))))]]
                   (my box Heap-addr))))

  (; Test creating a data instance and dropping it.
   ; The heap address is released.
   test-->> Dada-reduction
            (term (program_test Store_empty (seq ((var my-var = 22)
                                                  (var point = (data-instance Point () (22 33)))
                                                  (give (point))
                                                  0
                                                  ))))
            (term (program_test
                   [[(point expired) (my-var 22)]
                    []]
                   0)))

  (; Test creating a class instance that stores a data instance.
   ; The ref count is properly adjusted.
   test-->>E Dada-reduction
             (term (program_test Store_empty (seq ((var point = (data-instance Point () (22 33)))
                                                   (var vec = (class-instance Vec [(my Point ())] ((copy (point)))))
                                                   ))))
             (term (program_test
                    [[(vec (my box Heap-addr1))
                      (point (my box Heap-addr))]
                     [(Heap-addr (box 2 ((data Point) ((x 22) (y 33)))))
                      (Heap-addr1 (box 1 ((class Vec) ((value0 (my box Heap-addr))))))]]
                    0)))

  (; Test asserting the type of something.
   test-->> Dada-reduction
            (term (program_test Store_empty (seq ((var point = (data-instance Point () (22 33)))
                                                  (assert-ty (point) : (my Point ()))
                                                  ))))
            (term (program_test
                   [[(point (my box Heap-addr))]
                    [(Heap-addr (box 1 ((data Point) ((x 22) (y 33)))))
                     ]]
                   0)))

  (; Test sharing.
   test-->> Dada-reduction
            (term (program_test Store_empty (seq ((var point = (data-instance Point () (22 33)))
                                                  (var spoint = (share (point)))
                                                  ))))
            (term (program_test
                   [[(spoint (my box Heap-addr))
                     (point (my box Heap-addr))]
                    [(Heap-addr (box 2 ((data Point) ((x 22) (y 33)))))]]
                   0)))

  (; Test setting values.
   ;
   ; Note that the old value (Heap-addr) is dropped.
   test-->> Dada-reduction
            (term (program_test Store_empty (seq ((var point = (data-instance Point () (22 33)))
                                                  (set (point) = (data-instance Point () (44 66)))))))
            (term (program_test
                   [[(point (my box Heap-addr1))]
                    [(Heap-addr1 (box 1 ((data Point) ((x 44) (y 66)))))]
                    ]
                   0)))

  (; Test setting values to themselves.
   ;
   ; Here, the `give (point)` overwrites `point` (temporarily) with `expired`,
   ; so that when we drop the existing value, that's a no-op. Then we write the old
   ; value back into it.
   test-->> Dada-reduction
            (term (program_test Store_empty (seq ((var point = (data-instance Point () (22 33)))
                                                  (set (point) = (give (point)))))))
            (term (program_test
                   [[(point (my box Heap-addr))]
                    [(Heap-addr (box 1 ((data Point) ((x 22) (y 33)))))]
                    ]
                   0)))

  (; Test that sharing data clones-- otherwise, `point2` would be pointing at freed memory.
   test-->> Dada-reduction
            (term (program_test Store_empty (seq ((var point1 = (data-instance Point () (22 33)))
                                                  (var point2 = (share (point1)))
                                                  (set (point1) = (data-instance Point () (44 66)))
                                                  (copy (point2 x))))))
            (term (program_test
                   [[(point2 (my box Heap-addr))
                     (point1 (my box Heap-addr1))]
                    [(Heap-addr (box 1 ((data Point) ((x 22) (y 33)))))
                     (Heap-addr1 (box 1 ((data Point) ((x 44) (y 66)))))]
                    ]
                   22)))
  )
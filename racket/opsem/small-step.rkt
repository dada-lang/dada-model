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
  (define-syntax-rule
    ;; dada-seq-test
    ;;
    ;; Macro for testing a sequence check the state that we reach just before we pop the sequence.
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
    (dada-trace-test [expr ...] [var ...] [heap ...] [lease ...] value)
    (traces Dada-reduction (term (program_test Store_empty (seq (expr ...))))))

  (define-syntax-rule
    ;; dada-full-test
    ;;
    ;; Macro for testing a sequence check the state that we reach just before we pop the sequence.
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
  
  (test-->> Dada-reduction
            (term (program_test Store_empty (seq ())))
            (term (program_test Store_empty 0)))
  
  (test-->> Dada-reduction
            (term (program_test Store_empty (var my-var = 22)))
            (term (program_test (store-with-vars Store_empty (my-var 22)) 0)))
  
  (; Just before we pop the sequence, we have a stack segment with the two variables.
   dada-seq-test [(var my-var = 22) (var another-var = 44)]
                 [(my-var 22) (another-var 44)]
                 []
                 []
                 0)

  (; After giving `(another-var)`, its value becomes expired
   dada-seq-test
   ((var my-var = 22) (var another-var = 44) (give (another-var)))
   [(my-var 22) (another-var expired)]
   []
   []
   44)

  (; After copying `(another-var)`, its value remains
   dada-seq-test
   ((var my-var = 22) (var another-var = 44) (copy (another-var)))
   [(my-var 22) (another-var 44)]
   []
   []
   44)

  (; Test upcast
   dada-seq-test
   ((var my-var = 22) (var another-var = (44 : int)) (copy (another-var)))
   [(my-var 22) (another-var 44)]
   []
   []
   44)

  (; Test creating a data instance and copying it.
   ; The ref count winds up as 2.
   dada-seq-test
   ((var my-var = 22)
    (var point = (data-instance Point () (22 33)))
    (copy (point))
    )
   [(my-var 22) (point (my box Heap-addr))]
   [(Heap-addr (box 2 ((data Point) ((x 22) (y 33)))))]
   []
   (my box Heap-addr))

  (; Test creating a data instance and giving it.
   ; The ref count winds up as 1.
   dada-seq-test
   ((var my-var = 22)
    (var point = (data-instance Point () (22 33)))
    (give (point))
    )
   [(my-var 22) (point expired)]
   [(Heap-addr (box 1 ((data Point) ((x 22) (y 33)))))]
   []
   (my box Heap-addr))

  (; Test creating a data instance and dropping it.
   ; The heap address is released.
   dada-seq-test
   ((var my-var = 22)
    (var point = (data-instance Point () (22 33)))
    (give (point))
    0)
   [(my-var 22) (point expired)]
   []
   []
   0)

  (; Test creating a class instance that stores a data instance.
   ; The ref count is properly adjusted.
   dada-seq-test
   ((var point = (data-instance Point () (22 33)))
    (var vec = (class-instance Vec [(my Point ())] ((copy (point)))))
    )
   [(point (my box Heap-addr))
    (vec (my box Heap-addr1))
    ]    
   [(Heap-addr1 (box 1 ((class Vec) ((value0 (my box Heap-addr))))))
    (Heap-addr (box 2 ((data Point) ((x 22) (y 33)))))]
   []
   0)

  (; Test asserting the type of something.
   dada-seq-test
   [(var point = (data-instance Point () (22 33)))
    (assert-ty (point) : (my Point ()))]
   [(point (my box Heap-addr))]
   [(Heap-addr (box 1 ((data Point) ((x 22) (y 33)))))]
   []
   0)
  
  (; Test sharing a data instance (equivalent to cloning).
   dada-seq-test
   ((var point = (data-instance Point () (22 33)))
    (var spoint = (share (point))))
   [(point (my box Heap-addr))
    (spoint (my box Heap-addr))]
   [(Heap-addr (box 2 ((data Point) ((x 22) (y 33)))))]
   []
   0)
  
  (; Test setting values.
   ;
   ; Note that the old value (Heap-addr) is dropped.
   dada-seq-test
   [(var point = (data-instance Point () (22 33)))
    (set (point) = (data-instance Point () (44 66)))]
   [(point (my box Heap-addr1))]
   [(Heap-addr1 (box 1 ((data Point) ((x 44) (y 66)))))]
   []
   0)

  (; Test setting values to themselves.
   ;
   ; Here, the `give (point)` overwrites `point` (temporarily) with `expired`,
   ; so that when we drop the existing value, that's a no-op. Then we write the old
   ; value back into it.
   dada-seq-test
   [(var point = (data-instance Point () (22 33)))
    (set (point) = (give (point)))]
   [(point (my box Heap-addr))]
   [(Heap-addr (box 1 ((data Point) ((x 22) (y 33)))))]
   []
   0)

  (; Test that sharing data clones-- otherwise, `point2` would be pointing at freed memory.
   dada-seq-test
   ((var point1 = (data-instance Point () (22 33)))
    (var point2 = (share (point1)))
    (set (point1) = (data-instance Point () (44 66)))
    (copy (point2 x))
    )
   [(point1 (my box Heap-addr1))
    (point2 (my box Heap-addr))
    ]
   [(Heap-addr1 (box 1 ((data Point) ((x 44) (y 66)))))
    (Heap-addr (box 1 ((data Point) ((x 22) (y 33)))))
    ]
   []
   22)

  (; Test setting the value of a class instance that has data type
   dada-seq-test
   ((var vec1 = (class-instance Vec (int) (22)))
    (set (vec1 value0) = 44))
   [(vec1 (my box Heap-addr))]
   [(Heap-addr (box 1 ((class Vec) ((value0 44)))))]
   []
   0)
  
  (; Test borrowing a vector and mutating the field through the borrow.
   dada-seq-test
   ((var vec1 = (class-instance Vec (int) (22)))
    (var vec2 = (lend (vec1)))
    (set (vec2 value0) = 44))
   [(vec1 (my box Heap-addr))
    (vec2 ((leased Lease-id) box Heap-addr))
    ]
   [(Heap-addr (box 1 ((class Vec) ((value0 44)))))]
   [(Lease-id (borrowed () Heap-addr))]
   0)

  (; Test subleasing
   dada-seq-test
   ((var vec1 = (class-instance Vec (int) (22)))
    (var vec2 = (lend (vec1)))
    (var vec3 = (lend (vec2)))
    (set (vec3 value0) = 44))
   [(vec1 (my box Heap-addr))
    (vec2 ((leased Lease-id) box Heap-addr))
    (vec3 ((leased Lease-id1) box Heap-addr))
    ]
   [(Heap-addr (box 1 ((class Vec) ((value0 44)))))]
   [(Lease-id (borrowed () Heap-addr))
    (Lease-id1 (borrowed (Lease-id) Heap-addr))]
   0)

  (; Test lease cancellation
   dada-seq-test
   ((var vec1 = (class-instance Vec (int) (22)))
    (var vec2 = (lend (vec1)))
    (var vec3 = (lend (vec1)))
    (set (vec3 value0) = 44))
   [(vec1 (my box Heap-addr))
    (vec2 ((leased Lease-id) box Heap-addr))
    (vec3 ((leased Lease-id1) box Heap-addr))
    ]
   [(Heap-addr (box 1 ((class Vec) ((value0 44)))))]
   [(Lease-id1 (borrowed () Heap-addr))]
   0)

  (; Test lease cancellation on read--reading vec1
   ; cancels vec2/vec3
   dada-seq-test
   ((var vec1 = (class-instance Vec (int) (22)))
    (var vec2 = (lend (vec1)))
    (var vec3 = (lend (vec1)))
    (var v = (copy (vec1 value0))))
   [(vec1 (my box Heap-addr))
    (vec2 ((leased Lease-id) box Heap-addr))
    (vec3 ((leased Lease-id1) box Heap-addr))
    (v 22)
    ]
   [(Heap-addr (box 1 ((class Vec) ((value0 22)))))]
   []
   0)

  (; Test lease cancellation on read--reading vec2
   ; cancels vec2/vec3
   dada-seq-test
   ((var vec1 = (class-instance Vec (int) (22)))
    (var vec2 = (lend (vec1)))
    (var vec3 = (lend (vec2)))
    (var v = (copy (vec2 value0))))
   [(vec1 (my box Heap-addr))
    (vec2 ((leased Lease-id) box Heap-addr))
    (vec3 ((leased Lease-id1) box Heap-addr))
    (v 22)
    ]
   [(Heap-addr (box 1 ((class Vec) ((value0 22)))))]
   [(Lease-id (borrowed () Heap-addr))]
   0)

  (; Test that values introduced within a seq get dropped.
   dada-full-test
   ((var point1 = (data-instance Point () (22 33)))
    (var point2 = (share (point1)))
    (set (point1) = (data-instance Point () (44 66)))
    (copy (point2 x))
    )
   []
   []
   22)
  
  )
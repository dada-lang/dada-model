#lang racket

(require redex/reduction-semantics
         "../dada.rkt"
         "../opsem/traverse.rkt"
         "../util.rkt")



; How to generate a test
;
; * generate Inner:
;     * var inner = (class-instance String () ())
; * generate Inner-access
;     * if my { inner.give }
;     * if our { (share inner.give) }
;     * if lent { (inner.lend) }
;     * if shared { (inner.share) }
; * generate Outer:
;     * let C = if Field Type is var: use Some, else use Shared
;     * class-instance C (inner-access.give) }
; * generate Outer-access
;     * as above
; * analyze Outer-access value ?

(define-syntax-rule
  (dada-test-access-pattern inner-perm outer-perm field-perm result)

  (dada-let-store
   ((Store = ((var inner = (class-instance String () ()))
              (var inner-access = (dada-access-term inner-perm inner))
              (var outer = (class-instance (dada-class-name field-perm) () ((give (inner-access)))))
              (var outer-access = (dada-access-term outer-perm outer))
              ))
    (Traversal_0 (term (traversal program_test Store (outer-access value))))
    )
   (test-equal-terms (access-permissions Traversal_0)
                     result))

  )

(define-metafunction Dada
  dada-access-term : Permission x -> expr

  [(dada-access-term my x) (give (x))]
  [(dada-access-term our x) (share (give (x)))]
  [(dada-access-term (shared _) x) (share (x))]
  [(dada-access-term (lent _) x) (lend (x))]
  )

(define-metafunction Dada
  dada-class-name : mutability -> c

  [(dada-class-name var) Some]
  [(dada-class-name shared) Shared]
  [(dada-class-name atomic) Cell]
  )

; Patterns to test:
;
;                         Inner             Outer              Field type Yields
;                         --------------    -----------        ---------- ------
(dada-test-access-pattern our               (lent Lease-id)    var        (our ()       ()))
(dada-test-access-pattern our               (shared Lease-id)  var        (our ()       ()))
(dada-test-access-pattern our               my                 atomic     (our ()       ()))
(dada-test-access-pattern (shared Lease-id) (lent Lease-id1)   var        (our ()       (Lease-id)))
(dada-test-access-pattern (shared Lease-id) our                var        (our ()       (Lease-id)))
(dada-test-access-pattern (lent Lease-id)   my                 var        (my  ()       (Lease-id)))
(dada-test-access-pattern (lent Lease-id)   my                 shared     (our ()       (Lease-id)))
(dada-test-access-pattern (lent Lease-id)   our                var        (our ()       (Lease-id)))
(dada-test-access-pattern (lent Lease-id)   (shared Lease-id1) var        (our ()       (Lease-id Lease-id1)))
(dada-test-access-pattern (lent Lease-id)   (shared Lease-id1) atomic     (our (atomic) (Lease-id Lease-id1)))
(dada-test-access-pattern my                my                 var        (my  ()       ()))
(dada-test-access-pattern my                my                 shared     (our ()       ()))
(dada-test-access-pattern my                my                 atomic     (my  (atomic) ()))
(dada-test-access-pattern my                (lent Lease-id)    var        (my  ()       (Lease-id)))
(dada-test-access-pattern my                our                var        (our ()       ()))
(dada-test-access-pattern my                our                atomic     (our (atomic) ()))
(dada-test-access-pattern my                (shared Lease-id)  var        (our ()       (Lease-id)))
(dada-test-access-pattern my                (shared Lease-id)  atomic     (our (atomic) (Lease-id)))
#lang racket

(require redex/reduction-semantics
         "../dada.rkt"
         "../opsem/traverse.rkt"
         "../util.rkt"
         "../opsem/stack.rkt"
         "../opsem/lease.rkt")

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
  (dada-test-access-pattern inner-perm outer-perm field-perm result perm-sh-term (lease-id lease-kind-term lease-parents) ...)

  (dada-let-store
   ((Store = ((var inner = (class-instance String () ()))
              (var inner-access = (dada-access-term inner-perm inner))
              (var outer = (class-instance (dada-class-name field-perm) () ((give (inner-access)))))
              (var outer-access = (dada-access-term outer-perm outer))
              (var s = (share (outer-access value)))
              ))
    (Traversal_0 (term (traversal program_test Store (outer-access value))))
    ((Permission_sh box Address_sh) (term (var-in-store Store s)))
    )
   (pretty-print (term (inner-perm outer-perm field-perm)))
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
;                         Inner             Outer              Field type Yields                              Perm when shared   Lease contents
;                         --------------    -----------        ---------- ----------------------------------- ------------------ ----------------------------------------
(dada-test-access-pattern my                my                 var        (my  ()       ())                   (shared Lease-id)  (Lease-id shared ()))
(dada-test-access-pattern my                my                 shared     (our ()       ())                   our)
(dada-test-access-pattern my                my                 atomic     (my  (atomic) ())                   (shared Lease-id)  (Lease-id shared ()))
(dada-test-access-pattern my                (lent Lease-id)    var        (my  ()       (Lease-id))           (shared Lease-id1) (Lease-id1 shared (Lease-id)))
(dada-test-access-pattern my                (lent Lease-id)    shared     (our ()       (Lease-id))           (shared Lease-id1) (Lease-id1 shared (Lease-id)))
(dada-test-access-pattern my                (lent Lease-id)    atomic     (my  (atomic) (Lease-id))           (shared Lease-id1) (Lease-id1 shared (Lease-id)))
(dada-test-access-pattern my                our                var        (our ()       ())                   our)
(dada-test-access-pattern my                our                shared     (our ()       ())                   our)
(dada-test-access-pattern my                our                atomic     (our (atomic) ())                   (shared Lease-id)  (Lease-id shared ()))
(dada-test-access-pattern my                (shared Lease-id)  var        (our ()       (Lease-id))           (shared Lease-id)  (Lease-id shared ()))
(dada-test-access-pattern my                (shared Lease-id)  shared     (our ()       (Lease-id))           (shared Lease-id)  (Lease-id shared ()))
(dada-test-access-pattern my                (shared Lease-id)  atomic     (our (atomic) (Lease-id))           (shared Lease-id1) (Lease-id1 shared (Lease-id)))(dada-test-access-pattern our               my                 atomic     (our ()       ())                   our)
(dada-test-access-pattern (lent Lease-id)   my                 var        (my  ()       (Lease-id))           (shared Lease-id1) (Lease-id1 shared (Lease-id)))
(dada-test-access-pattern (lent Lease-id)   my                 shared     (our ()       (Lease-id))           (shared Lease-id1) (Lease-id1 shared (Lease-id)))
(dada-test-access-pattern (lent Lease-id)   my                 atomic     (my  (atomic) (Lease-id))           (shared Lease-id1) (Lease-id1 shared (Lease-id)))
(dada-test-access-pattern (lent Lease-id)   our                var        (our ()       (Lease-id))           (shared Lease-id1) (Lease-id1 shared (Lease-id)))
(dada-test-access-pattern (lent Lease-id)   our                shared     (our ()       (Lease-id))           (shared Lease-id1) (Lease-id1 shared (Lease-id)))
(dada-test-access-pattern (lent Lease-id)   our                atomic     (our (atomic) (Lease-id))           (shared Lease-id1) (Lease-id1 shared (Lease-id)))
(dada-test-access-pattern (lent Lease-id)   (shared Lease-id1) var        (our ()       (Lease-id Lease-id1)) (shared Lease-id2) (Lease-id2 shared (Lease-id Lease-id1)))
(dada-test-access-pattern (lent Lease-id)   (shared Lease-id1) shared     (our ()       (Lease-id Lease-id1)) (shared Lease-id2) (Lease-id2 shared (Lease-id Lease-id1)))
(dada-test-access-pattern (lent Lease-id)   (shared Lease-id1) atomic     (our (atomic) (Lease-id Lease-id1)) (shared Lease-id2) (Lease-id2 shared (Lease-id Lease-id1)))
(dada-test-access-pattern (lent Lease-id)   (lent Lease-id1)   var        (my  ()       (Lease-id Lease-id1)) (shared Lease-id2) (Lease-id2 shared (Lease-id Lease-id1)))
(dada-test-access-pattern (lent Lease-id)   (lent Lease-id1)   shared     (our ()       (Lease-id Lease-id1)) (shared Lease-id2) (Lease-id2 shared (Lease-id Lease-id1)))
(dada-test-access-pattern (lent Lease-id)   (lent Lease-id1)   atomic     (my  (atomic) (Lease-id Lease-id1)) (shared Lease-id2) (Lease-id2 shared (Lease-id Lease-id1)))
(dada-test-access-pattern our               my                 var        (our ()       ())                   our)
(dada-test-access-pattern our               my                 shared     (our ()       ())                   our)
(dada-test-access-pattern our               my                 atomic     (our ()       ())                   our)
(dada-test-access-pattern our               (lent Lease-id1)   var        (our ()       ())                   our)
(dada-test-access-pattern our               (lent Lease-id1)   shared     (our ()       ())                   our)
(dada-test-access-pattern our               (lent Lease-id1)   atomic     (our ()       ())                   our)
(dada-test-access-pattern our               our                var        (our ()       ())                   our)
(dada-test-access-pattern our               our                shared     (our ()       ())                   our)
(dada-test-access-pattern our               our                atomic     (our ()       ())                   our)
(dada-test-access-pattern our               (shared Lease-id1) var        (our ()       ())                   our)
(dada-test-access-pattern our               (shared Lease-id1) shared     (our ()       ())                   our)
(dada-test-access-pattern our               (shared Lease-id1) atomic     (our ()       ())                   our)
(dada-test-access-pattern (shared Lease-id) my                 var        (our ()       (Lease-id))           (shared Lease-id)  (Lease-id shared ()))
(dada-test-access-pattern (shared Lease-id) my                 shared     (our ()       (Lease-id))           (shared Lease-id)  (Lease-id shared ()))
(dada-test-access-pattern (shared Lease-id) my                 atomic     (our ()       (Lease-id))           (shared Lease-id)  (Lease-id shared ()))
(dada-test-access-pattern (shared Lease-id) (lent Lease-id1)   var        (our ()       (Lease-id))           (shared Lease-id)  (Lease-id shared ()))
(dada-test-access-pattern (shared Lease-id) (lent Lease-id1)   shared     (our ()       (Lease-id))           (shared Lease-id)  (Lease-id shared ()))
(dada-test-access-pattern (shared Lease-id) (lent Lease-id1)   atomic     (our ()       (Lease-id))           (shared Lease-id)  (Lease-id shared ()))
(dada-test-access-pattern (shared Lease-id) our                var        (our ()       (Lease-id))           (shared Lease-id)  (Lease-id shared ()))
(dada-test-access-pattern (shared Lease-id) our                shared     (our ()       (Lease-id))           (shared Lease-id)  (Lease-id shared ()))
(dada-test-access-pattern (shared Lease-id) our                atomic     (our ()       (Lease-id))           (shared Lease-id)  (Lease-id shared ()))
(dada-test-access-pattern (shared Lease-id) (shared Lease-id1) var        (our ()       (Lease-id))           (shared Lease-id)  (Lease-id shared ()))
(dada-test-access-pattern (shared Lease-id) (shared Lease-id1) shared     (our ()       (Lease-id))           (shared Lease-id)  (Lease-id shared ()))
(dada-test-access-pattern (shared Lease-id) (shared Lease-id1) atomic     (our ()       (Lease-id))           (shared Lease-id)  (Lease-id shared ()))

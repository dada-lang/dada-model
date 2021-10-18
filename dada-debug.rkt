#lang racket
(require redex/reduction-semantics
         "racket/dada.rkt"
         "racket/util.rkt"
         "racket/opsem/traverse.rkt")

(current-traced-metafunctions '())

(dada-test-give (lent Lease-id)   my                 var        (lent Lease-id1)   ((lent _) _ _) (Lease-id1 lent (Lease-id)))
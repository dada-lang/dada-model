#lang racket
(require redex/reduction-semantics)
(require "lease.rkt"
         "heap.rkt"
         "lang.rkt"
         "stack.rkt")
(provide test-store)

(define-metafunction Dada
  test-store : (Stack-mapping ...) (Heap-mapping ...) (Lease-mapping ...) -> Store

  [(test-store (Stack-mapping ...) (Heap-mapping ...) (Lease-mapping ...))
   (store-with-lease-mappings
    (store-with-heap-entries
     (store-with-vars (push-stack-segment Store_empty) Stack-mapping ...)
     Heap-mapping ...)
    (Lease-mapping ...))
   ]
  )
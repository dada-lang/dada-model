#lang racket
(require redex/reduction-semantics
         "racket/dada.rkt"
         "racket/util.rkt"
         "racket/opsem/traverse.rkt")

(current-traced-metafunctions '())

(dada-test-lend my                my                 shared     our)

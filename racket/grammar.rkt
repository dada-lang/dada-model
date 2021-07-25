#lang racket
(require redex)
(provide (all-defined-out))

(define-language Dada
  (program (class-definition ...) (struct-definition ...) (method-defn ...))
  (class-definition (class c (field-decl ...)))
  (struct-definition (struct s (field-decl ...)))
  (method-definition (fn m (var-decl ...) ty expr))
  (var-decl (x ty))
  (field-decl (f ty))
  (ty (mode c)
      s
      int
      (mode ty))
  (mode my own (shared (origin ...)) (borrowed (origin ...)))
  (access my own shared borrowed)
  (origin o)
  (expr (let var-decl = expr)
        (set place = expr)
        (call f (expr ...))
        (access place)
        number
        (seq expr ...)
        (dead x))
  (place (x f ...))
  (x variable-not-otherwise-mentioned)
  (m variable-not-otherwise-mentioned)
  (o variable-not-otherwise-mentioned)
  (s variable-not-otherwise-mentioned)
  (f variable-not-otherwise-mentioned)
  (c variable-not-otherwise-mentioned))

;; I can't figure out how to write these as real racket unit tests.

;(test-equal (redex-match Dada expr '(dead x)) (list '(match (bind 'expr '(dead x)))))
; (redex-match Dada expr '(seq (dead x)))
; (redex-match Dada expr '(seq (let (x int) = 22) (set (x) = 23) (call foo ((my (x)))) (dead x)))
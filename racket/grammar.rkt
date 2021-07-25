#lang racket
(require redex)
(provide (all-defined-out))

(define-language dada
  (program ((named-class-definition ...) (named-struct-definition ...) (named-method-defn ...)))
  (named-class-definition (c class-definition))
  (class-definition (class (field-decl ...)))
  (named-struct-definition (s struct-definition))
  (struct-definition (struct (field-decl ...)))
  (named-method-definition (m method-definition))
  (method-definition (fn (var-decl ...) -> ty expr))
  (var-decl (x ty))
  (field-decl (f ty))
  (ty (mode c)
      s
      int)
  (mode my our (shared (origin ...)) (borrowed (origin ...)))
  (access my our shared borrowed)
  (origin o)
  (expr (let var-decl = expr)
        (set place = expr)
        (call f (expr ...))
        (struct-instance s (expr ...))
        (class-instance c (expr ...))
        (access place)
        number
        (seq expr ...)
        (dead x))
  (places (place ...))
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

(test-match dada place (term (x0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Queries on the grammar

(define-metafunction dada
  the-structs : program -> (named-struct-definition ...)
  [(the-structs (_ (named-struct-definition ...) _))
   (named-struct-definition ...)]
  )

(define-metafunction dada
  struct-named : program s -> struct-definition
  [(struct-named program s) ,(cadr (assoc (term s) (term (the-structs program))))]
  )

(define-metafunction dada
  place-prefix : place -> place
  [(place-prefix (x f_0 ... f_1)) (x f_0 ...)])

(define-metafunction dada
  place-in : place places -> boolean
  [(place-in place places) ,(not (equal? #f (member (term place) (term places))))])

(define-metafunction dada
  place-or-prefix-in : place places -> boolean
  [(place-or-prefix-in place places)
   ,(or (term (place-in place places))
        (if (> (length (term place)) 1)
            (term (place-or-prefix-in (place-prefix place) places))
            #f))])

(let [(program
       (term (; classes:
              []
              ; structs:
              [(some-struct (struct [(f0 int) (f1 int)]))]
              ; methods:
              []
              )))]
  (test-equal (term (struct-named ,program some-struct)) (term (struct [(f0 int) (f1 int)])))
  (test-equal (term (place-prefix (x f1 f2 f3))) (term (x f1 f2)))
  (test-equal (term (place-or-prefix-in (x f1 f2 f3) ((x f1)))) #t)
  )

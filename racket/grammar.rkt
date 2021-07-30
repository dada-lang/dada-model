#lang racket
(require redex data/order "util.rkt")
(provide (all-defined-out))

(define-language dada
  (program ((named-class-definition ...) (named-struct-definition ...) (named-method-defn ...)))
  (named-class-definition (c class-definition))
  (class-definition (class generic-decls (field-decl ...)))
  (named-struct-definition (s struct-definition))
  (struct-definition (struct generic-decls (field-decl ...)))
  (named-method-definition (m method-definition))
  (method-definition (fn generic-decls (var-decl ...) -> ty expr))
  (generic-decls (generic-decl ...))
  (generic-decl (p variance))
  (variances (variance ...))
  (variance inout in out)
  (var-decl (x ty))
  (field-decl (f ty))
  (ty (mode c params)
      (s params)
      (mode p)
      int)
  (params (param ...))
  (param ty leases)
  (mode my our (shared leases))
  (access my our origin-kind)
  (origin-kind shared borrowed)
  (leases (lease ...))
  (lease (origin-kind place))
  (expr (let var-decl = expr)
        (set place = expr)
        (call f params (expr ...))
        (struct-instance s params (expr ...))
        (class-instance c params (expr ...))
        (access place)
        number
        (seq expr ...)
        (dead x))
  (places (place ...))
  (place (x f ...))
  (x variable-not-otherwise-mentioned) ; local variable
  (p variable-not-otherwise-mentioned) ; generic parameter name (of any kind: type/lease)
  (m variable-not-otherwise-mentioned) ; method name
  (s variable-not-otherwise-mentioned) ; struct name
  (f variable-not-otherwise-mentioned) ; field name
  (c variable-not-otherwise-mentioned)) ; class name

;; I can't figure out how to write these as real racket unit tests.

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
  struct-generic-decls : program s -> generic-decls
  [(struct-generic-decls program s)
   generic-decls
   (where (struct generic-decls _) (struct-named program s))]
  )

(define-metafunction dada
  struct-variances : program s -> (variance ...)
  [(struct-variances program s)
   (variance ...)
   (where ((p variance) ...) (struct-generic-decls program s))
   ])

(define-metafunction dada
  the-classes : program -> (named-class-definition ...)
  [(the-classes ((named-class-definition ...) _ _))
   (named-class-definition ...)]
  )

(define-metafunction dada
  class-named : program s -> class-definition
  [(class-named program s) ,(cadr (assoc (term s) (term (the-classes program))))]
  )

(define-metafunction dada
  class-generic-decls : program s -> generic-decls
  [(class-generic-decls program s)
   generic-decls
   (where (class generic-decls _) (class-named program s))]
  )

(define-metafunction dada
  class-variances : program s -> (variance ...)
  [(class-variances program s)
   (variance ...)
   (where ((p variance) ...) (class-generic-decls program s))
   ])

(define-metafunction dada
  generic-decls-index : generic-decls p -> number
  [(generic-decls-index generic-decls p)
   ,(- (length (term generic-decls)) (term number_p))
   (where number_p ,(length (assoc (term generic-decls) (term p))))])

(define-metafunction dada
  place-prefix : place -> place
  [(place-prefix (x f_0 ... f_1)) (x f_0 ...)])

(define-metafunction dada
  place-in : place places -> boolean
  [(place-in place_0 (place_1 ... place_0 place_2 ...)) #t]
  [(place-in place_0 places) #f])

(define-metafunction dada
  place-or-prefix-in : place places -> boolean
  [(place-or-prefix-in place places)
   ,(or (term (place-in place places))
        (if (> (length (term place)) 1)
            (term (place-or-prefix-in (place-prefix place) places))
            #f))])

(redex-let
 dada
 [(program
   (term (; classes:
          []
          ; structs:
          [(some-struct (struct ((t in) (u out)) [(f0 int) (f1 int)]))]
          ; methods:
          []
          )))]
 (test-equal-terms (struct-named program some-struct) (struct ((t in) (u out)) [(f0 int) (f1 int)]))
 (test-equal-terms (place-prefix (x f1 f2 f3)) (x f1 f2))
 (test-equal-terms (place-or-prefix-in (x f1 f2 f3) ((x f1))) #t)
 (test-equal-terms (struct-generic-decls program some-struct) ((t in) (u out)))
 (test-equal-terms (struct-variances program some-struct) (in out))
 )

(define (place<? place1 place2)
  ((order-<? datum-order) place1 place2))

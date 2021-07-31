#lang racket
(require redex data/order "util.rkt")
(provide (all-defined-out))

(define-language dada
  (program ((named-class-definition ...) (named-datatype-definition ...) (named-method-defn ...)))
  (named-class-definition (c class-definition))
  (class-definition (class generic-decls (field-decl ...)))
  (named-datatype-definition (dt datatype-definition))
  (datatype-definition (data generic-decls (field-decl ...)))
  (named-method-definition (m method-definition))
  (method-definition (fn generic-decls (var-decl ...) -> ty expr))
  (generic-decls (generic-decl ...))
  (generic-decl (p variance))
  (variances (variance ...))
  (variance inout in out)
  (var-decl (x ty))
  (field-decl (f ty))
  (ty (mode c params)
      (dt params)
      (mode p)
      (borrowed leases ty)
      int)
  (params (param ...))
  (param ty leases)
  (mode my (shared leases))
  (leases (lease ...))
  (lease (origin-kind place))
  (expr (let var-decl = expr)
        (set place = expr)
        (call f params (expr ...))
        (data-instance dt params (expr ...))
        (class-instance c params (expr ...))
        (share place)
        (lend place)
        (give place)
        number
        (seq expr ...)
        (dead x))
  (places (place ...))
  (place (x f ...))
  (x variable-not-otherwise-mentioned) ; local variable
  (p variable-not-otherwise-mentioned) ; generic parameter name (of any kind: type/lease)
  (m variable-not-otherwise-mentioned) ; method name
  (dt variable-not-otherwise-mentioned) ; datatype name
  (f variable-not-otherwise-mentioned) ; field name
  (c variable-not-otherwise-mentioned)) ; class name

;; I can't figure out how to write these as real racket unit tests.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Queries on the grammar

(define-metafunction dada
  the-datatypes : program -> (named-datatype-definition ...)
  [(the-datatypes (_ (named-datatype-definition ...) _))
   (named-datatype-definition ...)]
  )

(define-metafunction dada
  datatype-named : program dt -> datatype-definition
  [(datatype-named program dt) ,(cadr (assoc (term dt) (term (the-datatypes program))))]
  )

(define-metafunction dada
  datatype-generic-decls : program dt -> generic-decls
  [(datatype-generic-decls program dt)
   generic-decls
   (where (data generic-decls _) (datatype-named program dt))]
  )

(define-metafunction dada
  datatype-variances : program dt -> (variance ...)
  [(datatype-variances program dt)
   (variance ...)
   (where ((p variance) ...) (datatype-generic-decls program dt))
   ])

(define-metafunction dada
  the-classes : program -> (named-class-definition ...)
  [(the-classes ((named-class-definition ...) _ _))
   (named-class-definition ...)]
  )

(define-metafunction dada
  class-named : program dt -> class-definition
  [(class-named program dt) ,(cadr (assoc (term dt) (term (the-classes program))))]
  )

(define-metafunction dada
  class-generic-decls : program dt -> generic-decls
  [(class-generic-decls program dt)
   generic-decls
   (where (class generic-decls _) (class-named program dt))]
  )

(define-metafunction dada
  class-variances : program dt -> (variance ...)
  [(class-variances program dt)
   (variance ...)
   (where ((p variance) ...) (class-generic-decls program dt))
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
          ; datatypes:
          [(some-data (data ((t in) (u out)) [(f0 int) (f1 int)]))]
          ; methods:
          []
          )))]
 (test-equal-terms (datatype-named program some-data) (data ((t in) (u out)) [(f0 int) (f1 int)]))
 (test-equal-terms (place-prefix (x f1 f2 f3)) (x f1 f2))
 (test-equal-terms (place-or-prefix-in (x f1 f2 f3) ((x f1))) #t)
 (test-equal-terms (datatype-generic-decls program some-data) ((t in) (u out)))
 (test-equal-terms (datatype-variances program some-data) (in out))
 )

(define (place<? place1 place2)
  ((order-<? datum-order) place1 place2))

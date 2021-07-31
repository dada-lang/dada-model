#lang racket
(require redex data/order "util.rkt")
(provide (all-defined-out))

(define-language dada
  (program ((named-class-definition ...) (named-datatype-definition ...) (named-method-defn ...)))
  (named-class-definition (c class-definition))
  (class-definition (class generic-decls field-decls))
  (named-datatype-definition (dt datatype-definition))
  (datatype-definition (data generic-decls field-decls))
  (named-method-definition (m method-definition))
  (method-definition (fn generic-decls (var-decl ...) -> ty expr))
  (generic-decls (generic-decl ...))
  (generic-decl (p variance))
  (variances (variance ...))
  (variance inout in out)
  (var-decl (x ty))
  (field-decls (field-decl ...))
  (field-decl (f ty))
  (ty (mode c params)
      (dt params)
      (mode p)
      (mode borrowed leases ty)
      int)
  (params (param ...))
  (param ty leases)
  (mode my (shared leases))
  (leases (lease ...))
  (lease (lease-kind place))
  (lease-kind shared borrowed)
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
        (drop x))
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

;; assoc-value k pairs
;;
;; Finds the value v from assoc list ((k v) ...)
(define (assoc-value k pairs)
  (cadr (assoc k pairs)))

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
  datatype-field-ty : program dt f -> ty
  [(datatype-field-ty program dt f)
   ty
   (where (data _ (field-decl_0 ... (f ty) field-decl_1 ...)) (datatype-named program dt))
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
  class-variances : program c -> (variance ...)
  [(class-variances program c)
   (variance ...)
   (where ((p variance) ...) (class-generic-decls program c))
   ])

(define-metafunction dada
  class-field-ty : program c f -> ty
  [(class-field-ty program c f)
   ty
   (where (class _ (field-decl_0 ... (f ty) field-decl_1 ...)) (class-named program c))
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
          [
           (String (class () ()))
           (Character (class () ((hp int) (name (my String ())) (ac int))))
           ]
          ; datatypes:
          [
           (some-data (data ((t in) (u out)) [(f0 int) (f1 int)]))
           (Point (data () ((x int) (y int))))
           (Some (data ((E out)) ((value (my E)))))
           ]
          ; methods:
          []
          )))]
 (test-equal-terms (datatype-named program some-data) (data ((t in) (u out)) [(f0 int) (f1 int)]))
 (test-equal-terms (place-prefix (x f1 f2 f3)) (x f1 f2))
 (test-equal-terms (place-or-prefix-in (x f1 f2 f3) ((x f1))) #t)
 (test-equal-terms (datatype-generic-decls program some-data) ((t in) (u out)))
 (test-equal-terms (datatype-variances program some-data) (in out))
 (test-equal-terms (datatype-field-ty program Point x) int)
 (test-equal-terms (datatype-field-ty program Some value) (my E))
 (test-equal-terms (class-field-ty program Character hp) int)
 (test-equal-terms (class-field-ty program Character ac) int)
 (test-equal-terms (class-field-ty program Character name) (my String ())) 
 )

(define (place<? place1 place2)
  ((order-<? datum-order) place1 place2))

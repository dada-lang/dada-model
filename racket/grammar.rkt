#lang racket
(require redex data/order "util.rkt")
(provide (all-defined-out))

(define-language dada
  (program ((named-class-definition ...) (named-method-definition ...)))
  (named-class-definition (c class-definition))
  (class-definition (class generic-decls class-field-decls))
  (named-method-definition (m method-definition))
  (method-definition (fn method-signature = expr))
  (method-signature (generic-decls var-tys -> ty))
  (generic-decls (generic-decl ...))
  (generic-decl (p variance))
  (variances (variance ...))
  (variance inout in out)
  (var-tys (var-ty ...))
  (var-ty (x ty))
  (class-field-decls (class-field-decl ...))
  (class-field-decl (mutability f ty))
  (mutability shared var atomic)
  (atomic? () (atomic))
  (tys (ty ...))
  (ty (mode c params)
      (mode p)
      (mode borrowed leases ty)
      int)
  (params (param ...))
  (param ty leases)
  (mode my (shared leases))
  (leases (lease ...))
  (lease (lease-kind place) p atomic expired)
  (lease-kind shared borrowed)
  (exprs (expr ...))
  (expr (var x = expr)
        (set place-at-rest = expr)
        (call m params exprs)
        (class-instance c params exprs)
        (share place-at-rest)
        (lend place-at-rest)
        (give place-at-rest)
        (copy place-at-rest)
        number
        (seq exprs)
        (atomic expr)
        (expr : ty)
        (assert-ty place-at-rest : ty))
  (places (place ...))
  (place (pb f ...))
  (place-at-rest (x f ...))
  (fs (f ...))
  (xs (x ...))
  (pb in-flight x)
  (x id) ; local variable
  (p id) ; generic parameter name (of any kind: type/lease)
  (m id) ; method name
  (f id) ; field name
  (c id) ; class name
  (ids (id ...))
  (id variable-not-otherwise-mentioned)
  )

(define-metafunction dada
  ;; Useful metafunction to assert that something is
  ;; true -- if it is false, you'll get an error.
  assert : boolean -> boolean
  [(assert #t) #t])

(define-metafunction dada
  any? : boolean ... -> boolean

  [(any? boolean_0 ... #t boolean_1 ...) #t]
  [(any? #f ...) #f]
  )

(define-metafunction dada
  all? : boolean ... -> boolean

  [(all? boolean_0 ... #f boolean_1 ...) #f]
  [(all? #t ...) #t]
  )

(define-metafunction dada
  not? : boolean -> boolean

  [(not? #t) #f]
  [(not? #f) #t]
  )

;; defined? any
;;
;; True for all values. Useful for testing whether a
;; metafunction like `place-ty` can successfully execute
;; as part of an invariant.
(define-metafunction dada
  defined? : any -> boolean

  [(defined? _) #t]
  )

(define-metafunction dada
  any-atomic? : atomic? ... -> atomic?

  [(any-atomic? () ...) ()]
  [(any-atomic? atomic? ... (atomic) atomic? ...) (atomic)]
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Queries on the grammar

;; assoc-value k pairs
;;
;; Finds the value v from assoc list ((k v) ...)
(define (assoc-value k pairs)
  (cadr (assoc k pairs)))

(define-metafunction dada
  the-classes : program -> (named-class-definition ...)
  [(the-classes ((named-class-definition ...) _))
   (named-class-definition ...)]
  )

(define-metafunction dada
  class-named : program c -> class-definition
  [(class-named program c)
   class-definition
   (where (_ ... (c class-definition) _ ...) (the-classes program))]
  )

(define-metafunction dada
  class-generic-decls : program c -> generic-decls
  [(class-generic-decls program c)
   generic-decls
   (where (class generic-decls _) (class-named program c))]
  )

(define-metafunction dada
  class-variances : program c -> (variance ...)
  [(class-variances program c)
   (variance ...)
   (where ((p variance) ...) (class-generic-decls program c))
   ])

(define-metafunction dada
  class-field-names : program c -> fs
  [(class-field-names program c)
   (f ...)
   (where (class _ ((_ f _) ...)) (class-named program c))
   ]
  )

(define-metafunction dada
  class-field-ty : program c f -> ty
  [(class-field-ty program c f)
   ty
   (where (class _ (class-field-decl_0 ... (_ f ty) class-field-decl_1 ...)) (class-named program c))
   ])

(define-metafunction dada
  class-field-var-tys : program c -> var-tys
  [(class-field-var-tys program c)
   ((f ty) ...)
   (where (class _ ((_ f ty) ...)) (class-named program c))
   ])

(define-metafunction dada
  class-field-mutability : program c f -> mutability
  [(class-field-mutability program c f)
   mutability
   (where (class _ (class-field-decl_0 ... (mutability f _) class-field-decl_1 ...)) (class-named program c))
   ])

;; class-field-non-atomic? program c f
;;
;; True if c::f is either shared or var, false if atomic.
;; In other words, true when `f` is frozen when shared.
(define-metafunction dada
  class-field-non-atomic? : program c f -> boolean
  [(class-field-non-atomic? program c f) #f (where atomic (class-field-mutability program c f))]
  [(class-field-non-atomic? program c f) #t (where var (class-field-mutability program c f))]
  [(class-field-non-atomic? program c f) #t (where shared (class-field-mutability program c f))]
  )

;; class-field-atomic? program c f
;;
;; True if c::f is declared as atomic
(define-metafunction dada
  class-field-atomic? : program c f -> boolean

  [(class-field-atomic? program c f) #t (where atomic (class-field-mutability program c f))]
  [(class-field-atomic? program c f) #f (where var (class-field-mutability program c f))]
  [(class-field-atomic? program c f) #f (where shared (class-field-mutability program c f))]
  )

(define-metafunction dada
  class-field-shared? : program c f -> boolean
  [(class-field-shared? program c f) #f (where atomic (class-field-mutability program c f))]
  [(class-field-shared? program c f) #f (where var (class-field-mutability program c f))]
  [(class-field-shared? program c f) #t (where shared (class-field-mutability program c f))]
  )

(define-metafunction dada
  class-field-mutable? : program c f -> boolean
  [(class-field-mutable? program c f) #t (where atomic (class-field-mutability program c f))]
  [(class-field-mutable? program c f) #t (where var (class-field-mutability program c f))]
  [(class-field-mutable? program c f) #f (where shared (class-field-mutability program c f))]
  )

(define-metafunction dada
  not-atomic? : mutability -> boolean
  [(not-atomic? atomic) #f]
  [(not-atomic? _) #t])

(define-metafunction dada
  mutable? : mutability -> boolean
  [(mutable? shared) #f]
  [(mutable? _) #t])

(define-metafunction dada
  generic-decls-index : generic-decls p -> number
  [(generic-decls-index generic-decls p)
   ,(- (length (term generic-decls)) (term number_p))
   (where number_p ,(length (assoc (term generic-decls) (term p))))])

(define-metafunction dada
  field-names : program ty -> fs
  [(field-names program int) ()]
  [(field-names program (mode p)) ()]
  [(field-names program (mode borrowed leases ty)) (field-names program ty)]
  [(field-names program (mode c params)) (class-field-names program c)]
  )

(define-metafunction dada
  ty-field-mutability : program ty f -> mutability

  [(ty-field-mutability program (_ c _) f)
   (class-field-mutability program c f)
   ]

  [(ty-field-mutability program (_ borrowed _ ty) f)
   (ty-field-mutability program ty f)
   ]
  )

(define-metafunction dada
  place-prefix : place -> place
  [(place-prefix (pb f_0 ... f_1)) (pb f_0 ...)])

(define-metafunction dada
  place-in? : place places -> boolean
  [(place-in? place_0 (place_1 ... place_0 place_2 ...)) #t]
  [(place-in? place_0 places) #f])

(define-metafunction dada
  place-or-prefix-in? : place places -> boolean
  [(place-or-prefix-in? place_1 (place_2 ...))
   (any? (place-contains? place_2 place_1) ...)])

(define-metafunction dada
  places-proper-subset? : places places -> boolean
  [(places-proper-subset? places_1 places_2)
   ,(begin (pretty-print (term ("subset" places_1 places_2))) (proper-subset? (term places_1) (term places_2)))
   ]
  )

;; place-contains place_1 place_2
;;
;; True if place_1 contains all of place_2. This is true if
;; place_1 is a prefix of place_2. E.g., `a.b` contains `a.b.c`
;; but not vice-versa.
(define-metafunction dada
  place-contains? : place place -> boolean

  ;; place-0 is a prefix of place-1
  [(place-contains? (pb_0 f_0 ...) (pb_0 f_0 ... f_1 ...)) #t]
  ;; disjoint places
  [(place-contains? place_0 place_1) #f]
  )

;; places-overlapping place_1 place_2
;;
;; True if place_1 and place_2 refer to overlapping bits of memory.
(define-metafunction dada
  places-overlapping? : place place -> boolean

  ;; place-0 is a prefix of place-1
  [(places-overlapping? (pb_0 f_0 ...) (pb_0 f_0 ... f_1 ...)) #t]
  ;; place-0 is a suffix of place-1
  [(places-overlapping? (pb_0 f_0 ... f_1 ...) (pb_0 f_0 ...)) #t]
  ;; disjoint places
  [(places-overlapping? place_0 place_1) #f]
  )

(define-metafunction dada
  shared-mode? : mode -> boolean

  [(shared-mode? my) #f]
  [(shared-mode? (shared _)) #t])

(define-metafunction dada
  method-named : program m -> method-definition
  [(method-named program m)
   method-definition
   (where (_ (named-method-definition_0 ... (m method-definition) named-method-definition_1 ...)) program)]
  )

(define-metafunction dada
  signature-for-method-named : program m -> method-signature
  [(signature-for-method-named program m)
   method-signature
   (where (fn method-signature = expr) (method-named program m))]
  )

(define-term our (shared ()))
(test-match dada mode (term our))

;; useful test program
(define-term
  program_test
  ([(String (class () ()))
    (Pair (class ((A out) (B out)) ((var a (my A)) (var b (my B)))))
    (Vec (class ((E out)) ((var value0 (my E)))))
    (Fn (class ((A in) (R out)) ()))
    (Cell (class ((T inout)) ((atomic value (my T)))))
    (Character (class () ((var hp int) (shared name (my String ())) (var ac int))))
    (ShVar (class ((T in)) ((var shv (our T)))))
    (Message (class ((E out)) ((shared vec (my Vec ((my E)))) (var element ((shared ((shared (vec)))) E)))))
    (Some (class ((E out)) ((var value (my E)))))
    (Option (class ((T out)) ()))
    (Point (class () ((shared x int) (shared y int))))
    ]
   []))
(test-match dada program (term program_test))

(define-metafunction
  dada
  program-with-methods : program named-method-definition ... -> program

  [(program-with-methods program named-method-definition_new ...)
   ((named-class-definition ...) (named-method-definition ... named-method-definition_new ...))
   (where ((named-class-definition ...) (named-method-definition ...)) program)]
  )

(define (place<? place1 place2)
  ((order-<? datum-order) place1 place2))

(module+ test
  (test-equal-terms (place-prefix (x f1 f2 f3)) (x f1 f2))
  (test-equal-terms (place-or-prefix-in? (x f1 f2 f3) ((x f1))) #t)
  (test-equal-terms (place-or-prefix-in? (x f1 f2 f3) ((x g1))) #f)
  (test-equal-terms (class-field-ty program_test Character hp) int)
  (test-equal-terms (class-field-ty program_test Character ac) int)
  (test-equal-terms (class-field-ty program_test Character name) (my String ()))
  (test-equal-terms (places-overlapping? (x f1 f2) (x f1 f2 f3)) #t)
  (test-equal-terms (places-overlapping? (x f1 f2) (x f1 f2)) #t)
  (test-equal-terms (places-overlapping? (x f1 f2 f3) (x f1 f2)) #t)
  (test-equal-terms (places-overlapping? (x f1 f2) (x f1 f3)) #f)
  (test-equal-terms (place-contains? (x f1 f2) (x f1 f2 f3)) #t)
  (test-equal-terms (place-contains? (x f1 f2) (x f1 f2)) #t)
  (test-equal-terms (place-contains? (x f1 f2 f3) (x f1 f2)) #f)
  (test-equal-terms (place-contains? (x f1 f2) (x f1 f3)) #f)
  (test-equal-terms (field-names program_test (my Character ())) (hp name ac))
  (test-equal-terms (field-names program_test (my Point ())) (x y))
  (test-equal-terms (field-names program_test (my Some ((my Point ())))) (value))
  )



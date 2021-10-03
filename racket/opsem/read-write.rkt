#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         "../grammar.rkt"
         "../type-system.rkt"
         "../util.rkt"
         "lang.rkt"
         "clone.rkt"
         "stack.rkt"
         "heap.rkt"
         "lease.rkt")

(provide read-place
         write-place
         share-place
         lend-place
         move-place)

(define-metafunction Dada
  load-field : Store Unboxed-value f -> Value
  [(load-field Store (_ (_ ... (f Value) _ ...)) f) Value]
  )

(define-metafunction Dada
  ;; deref
  ;;
  ;; Derefs through any boxes
  deref : Store Unboxed-value -> Unboxed-value
  [(deref Store (_ box Address)) (deref Store (load-heap Store Address))]
  [(deref Store Unboxed-value) Unboxed-value]
  )

(define-metafunction Dada
  ;; move-place
  ;;
  ;; Reads the value stored at the given place.
  ;;
  ;; Returns the value along with the set of leases that were traversed to reach it.
  move-place : Store place -> (Value Store)

  [; moving an integer: just copy it, doesn't matter where we found it
   ; for now, we'll expire the old location, hence treating data as "owned" content
   ; and not leased, but this is debatable
   (move-place Store place)
   (number Store_out)
   (where (number _ Store_read) (read-place Store place))
   (where/error Store_out (write-place Store_read place expired))
   ]

  [; moving an owned value:
   ; - give back an exact copy of the value
   ; - overwrite the old value with expired, to keep ref count etc correct
   (move-place Store place)
   ((my box Address) Store_out)
   (where ((my box Address) () Store_read) (read-place Store place))
   (where/error Store_out (write-place Store_read place expired))
   ]

  [; moving a leased value:
   ; - create a sublease
   (move-place Store place)
   (lease-or-sublease-value Store_read shared Value Leases)
   (where/error (Value Leases Store_read) (read-place Store place))
   ]

  )

(define-metafunction Dada
  ;; lease-or-sublease-value
  ;;
  ;; Given a (boxed) value `Value` found by traversing the leases `Leases`,
  ;; creates a sublease of `Value`.
  ;;
  ;; If the list `Leases` is empty,
  ;; then creates a fresh lease of kind `Lease-kind`.
  lease-or-sublease-value : Store Lease-kind Value Leases -> (Value Store)

  [(lease-or-sublease-value Store Lease-kind_default (Ownership box Address) Leases_traversed)
   (lease-or-sublease-box Store Lease-kind_default Address Leases_addr)
   (where/error Leases_addr (leases-after-traversing Store Leases_traversed Ownership))
   ]

  )

(define-metafunction Dada
  ;; lease-or-sublease-box
  ;;
  ;; When we move a leased place, we typically create a "sublease".
  ;; As an optimization, if the place is leased from a single shared lease,
  ;; we can just duplicate it.
  lease-or-sublease-box : Store Lease-kind_default Address Leases -> (Value Store)

  #;[(lease-or-sublease-box Store Lease-kind_default Address Leases)
     ()
     (where 22 ,(pretty-print (term ("lease-or-sublease-box" Store Lease-kind_default Address Leases))))]

  [; optimization: if the list has exactly 1 shared lease, just copy it
   (lease-or-sublease-box Store _ Address (Lease))
   (((leased Lease) box Address) Store)
   (where shared (kind-of-lease Store Lease))
   ]

  [; otherwise, we create a sublease
   (lease-or-sublease-box Store Lease-kind_default Address Leases)
   (((leased Lease_sub) box Address) Store_out)
   (where/error Lease-kind (lease-or-sublease-kind Store Lease-kind_default Leases))
   (where/error (Lease_sub Store_out) (create-lease-mapping Store Lease-kind Leases Address))
   ]
  )

(define-metafunction Dada
  ;; lease-or-sublease-kind
  ;;
  ;; When subleasing a place, if there is *any* shared sublease in the list, then
  ;; we must make a shared sublease ourselves.
  lease-or-sublease-kind : Store Lease-kind_default Leases -> Lease-kind

  [; Empty lease list: use default
   (lease-or-sublease-kind Store Lease-kind_default ())
   Lease-kind_default
   ]

  [; Any shared leases? Use shared
   (lease-or-sublease-kind Store _ (Lease_0 ... Lease_1 Lease_2 ...))
   shared
   (where shared (kind-of-lease Store Lease_1))
   ]

  [; Only lent leases: Use lent
   (lease-or-sublease-kind Store _ _)
   lent
   ]

  )

(define-metafunction Dada
  ;; read-place
  ;;
  ;; Reads the value stored at the given place.
  ;;
  ;; Returns the value along with the set of leases that were traversed to reach it.
  read-place : Store place -> (Value Leases Store)

  #;[(read-place Store place)
     ()
     (where 22 ,(pretty-print (term ("read-place" Store place))))]

  [(read-place Store (x f ...)) (read-fields Store () (var-in-store Store x) (f ...))]
  )

(define-metafunction Dada
  read-fields : Store Leases Unboxed-value (f ...) -> (Value Leases Store)

  #;[(read-fields Store Leases Unboxed-value (f ...))
     ()
     (where 22 ,(pretty-print (term ("read-fields" Store Leases Unboxed-value (f ...)))))]

  [(read-fields Store Leases Value ()) (Value Leases Store)]

  [(read-fields Store Leases (Ownership box Address) (f_0 f_1 ...))
   (read-fields Store_read Leases_out Unboxed-value (f_0 f_1 ...))
   (where/error Leases_out (leases-after-traversing Store Leases Ownership))
   (where/error (Unboxed-value Store_read) (load-and-invalidate-heap Store Ownership Address))
   ]

  [(read-fields Store Leases Unboxed-value (f_0 f_1 ...))
   (read-fields Store Leases Unboxed-value_0 (f_1 ...))
   (where/error Unboxed-value_0 (load-field Store Unboxed-value f_0))])

(define-metafunction Dada
  ;; leases-after-traversing
  ;;
  ;; Used when traversing through a place `(a b c ... z)`
  ;;
  ;;     a --ownership_0--> b --ownership_1 --> c --> ... --ownership_n --> z
  ;;
  ;; As we traverse, we accumulate a set `Leases` of leases that
  ;; are needed to "secure" the value we have reached. This function
  ;; modifies that set to account for the `Ownership` of the next link
  ;; to be added:
  ;;
  ;; * traversing into a value shared with lease `Lease` means we only need `{Lease}`
  ;; * traversing into a lent value with lease `Lease` adds `Lease` to the set
  ;; * traversing into an owned value leaves the set unchanged
  ;;
  ;; Effectively `Leases` are the set of leases that secure the location
  ;; where this reference was found, and `Ownership` is the ownership
  ;; of the reference. Shared references are independent of
  ;; place they are located, so they reset the set of `Leases`.
  leases-after-traversing : Store Leases Ownership -> Leases

  #;[(leases-after-traversing Store Leases Ownership)
     ()
     (where 22 ,(pretty-print (term ("leases-after-traversing" Store Leases Ownership))))]

  [(leases-after-traversing Store Leases my) Leases]

  [(leases-after-traversing Store Leases (leased Lease))
   (Lease)
   (where shared (kind-of-lease Store Lease))]

  [(leases-after-traversing Store (Lease_in ...) (leased Lease))
   (Lease_in ... Lease)
   (where lent (kind-of-lease Store Lease))]

  )

(define-metafunction Dada
  ;; load-and-invalidate-heap
  ;;
  ;; Reads the value stored at the given place.
  ;;
  ;; Returns the value along with the set of leases that were traversed to reach it.
  load-and-invalidate-heap : Store Ownership Address -> (Unboxed-value Store)

  [(load-and-invalidate-heap Store Ownership Address)
   (Unboxed-value Store_out)
   (where/error Unboxed-value (load-heap Store Address))
   (where/error Store_out (invalidate-leases-in-store Store (read-address Ownership Address)))]
  )

(define-metafunction Dada
  write-place : Store place Value_new -> Store

  [(write-place Store (x f ...) Value_new)
   Store_out
   (where/error Value_0 (var-in-store Store x))
   (where/error (Value_1 Store_1) (write-fields Store Value_0 (f ...) Value_new))
   (where/error Store_out (store-with-updated-var Store_1 x Value_1))]
  )

(define-metafunction Dada
  write-fields : Store Unboxed-value_old (f ...) Value_new -> (Unboxed-value Store)

  [(write-fields Store _ () Value_new)
   (Value_new Store)]

  [(write-fields Store (Ownership box Address) (f_0 f_1 ...) Value_new)
   ((Ownership box Address) Store_3)
   (where/error Unboxed-value_0 (load-heap Store Address))
   (where/error (Unboxed-value_1 Store_1) (write-fields Store Unboxed-value_0 (f_0 f_1 ...) Value_new))
   (where/error Store_2 (store-heap Store_1 Address Unboxed-value_1))
   (where/error Store_3 (invalidate-leases-in-store Store_2 (write-address Ownership Address)))]

  [(write-fields Store (Aggregate-id (Field-value_0 ... (f_0 Value_f0_old) Field-value_1 ...)) (f_0 f_1 ...) Value_new)
   ((Aggregate-id (Field-value_0 ... (f_0 Value_f0_new) Field-value_1 ...)) Store_f0_new)
   (where/error (Value_f0_new Store_f0_new) (write-fields Store Value_f0_old (f_1 ...) Value_new))]

  )

(define-metafunction Dada
  write-action : Ownership Address -> Action

  [(write-action my Address) (write-address Address)]
  [(write-action (leased Lease) Address) (write-lease Lease)]
  )

(define-metafunction Dada
  share-place : Store place -> (Value Store)

  [(share-place Store place)
   (share-value Store_0 Leases_0 Value_0)
   (where/error (Value_0 Leases_0 Store_0) (read-place Store place))]
  )

(define-metafunction Dada
  share-value : Store Leases Value -> (Value Store)

  [; sharing a number just copies it
   (share-value Store Leases number)
   (number Store)
   ]

  [; share a class
   (share-value Store Leases (Ownership box Address))
   (lease-or-sublease-value Store shared (Ownership box Address) Leases)
   ]
  )

(define-metafunction Dada
  lend-place : Store place -> (Value Store)

  [; Lend out a class (the only thing we can lend out)
   (lend-place Store place)
   (lease-or-sublease-value Store_read lent Value Leases_read)
   (where/error (Value Leases_read Store_read) (read-place Store place))
   ]

  )

(module+ test
  (redex-let*
   Dada
   [(Stack-mappings (term [(x0 (my box an-int))
                           (x1 (my box struct-1))
                           (x2 (my box struct-2))
                           (x4 (my box class-1))]))
    (Store
     (term ([Stack-mappings]
            [(an-int (box 3 22))
             (another-int (box 1 44))
             (struct-1 (box 1 ((class some-struct) [(f0 (my box an-int)) (f1 (my box struct-2))])))
             (struct-2 (box 2 ((class another-struct) [(f0 66)])))
             (class-1 (box 1 ((class some-class) [(f0 88)])))]
            [])))
    ]

   (test-equal-terms (deref Store (var-in-store Store x0))
                     22)
   (test-equal-terms (var-in-store Store x1)
                     (my box struct-1))
   (test-equal-terms (deref Store (var-in-store Store x1))
                     ((class some-struct) [(f0 (my box an-int)) (f1 (my box struct-2))]))
   (test-equal-terms (read-place Store (x1 f0))
                     ((my box an-int) () Store))
   (test-match-terms Dada
                     (read-place (write-place Store (x1 f0) (my box another-int)) (x1 f0))
                     ((my box another-int) () Store))

   (test-equal-terms (read-place Store (x2 f0))
                     (66 () Store))
   (test-match-terms Dada
                     (read-place (write-place Store (x2 f0) 88) (x2 f0))
                     (88 () _))


   (; sharing a boxed integer -- it's unclear if this will be a thing in dada in the end,
    ; for now we'll assume that the box should be leased, but maybe it could be cloned.
    test-match-terms Dada (share-place Store (x0)) (((leased Lease-id) box an-int) [_ (_ ... (an-int (box 3 22)) _ ...) _]))

   (test-equal-terms (share-place Store (x2 f0)) (66 Store))
   (test-match-terms Dada
                     (share-place Store (x4))
                     (((leased Lease-id) box class-1) [_ _ [(Lease-id (shared () class-1))]]))
   )
  )
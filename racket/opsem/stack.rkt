#lang racket
;; Convention: uppercase names are things that only exist at runtime

(require redex
         "../util.rkt"
         "lang.rkt")
(provide store-with-vars
         store-with-var
         var-in-store
         store-with-updated-var
         push-stack-segment
         pop-stack-segment
         stack-segments-in-store)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic memory access metafunctions

(define-metafunction Dada
  ;; stack-segments-in-store
  ;;
  ;; Return the stack segments from the store.
  stack-segments-in-store : Store -> Stack-segments
  [(stack-segments-in-store (Stack-segments _ _))
   Stack-segments])

(define-metafunction Dada
  ;; store-with-stack-segments
  ;;
  ;; Return the stack segments from the store.
  store-with-stack-segments : Store Stack-segments -> Store
  [(store-with-stack-segments (Stack-segments_0 Heap-mappings Lease-mappings) Stack-segments_1)
   (Stack-segments_1 Heap-mappings Lease-mappings)])

(define-metafunction Dada
  ;; var-in-store
  ;;
  ;; Read the Value for a given variable from the stack.
  var-in-store : Store x -> Value
  [(var-in-store Store x)
   (var-in-stack-segments (stack-segments-in-store Store) x)])

(define-metafunction Dada
  ;; var-in-stack-segments
  ;;
  ;; Read the Value for a given variable from the stack.
  var-in-stack-segments : Stack-segments x -> Value

  [; Is the left-most variable named x?
   (var-in-stack-segments (((x Value) Stack-mapping ...) Stack-segment ...) x)
   Value]

  [; Else, drop the left-most variable
   (var-in-stack-segments ((_ Stack-mapping ...) Stack-segment ...) x)
   (var-in-stack-segments ((Stack-mapping ...) Stack-segment ...) x)]

  [; Drop the left-most segment, if it is empty
   (var-in-stack-segments (() Stack-segment_1 ...) x)
   (var-in-stack-segments (Stack-segment_1 ...) x)]

  )

(define-metafunction Dada
  ;; store-with-var
  ;;
  ;; Introduce a variable with a given Value into the top stack segment.
  store-with-var : Store x Value -> Store
  [(store-with-var Store x Value)
   (store-with-stack-segments Store Stack-segments_out)
   (where/error ((Stack-mapping ...) Stack-segment ...) (stack-segments-in-store Store))
   (where/error Stack-segments_out (((x Value) Stack-mapping ...) Stack-segment ...))
   ]

  )

(define-metafunction Dada
  ;; store-with-vars
  ;;
  ;; Introduce a variable with a given Value into the top stack segment.
  store-with-vars : Store (x Value) ... -> Store

  [(store-with-vars Store) Store]

  [(store-with-vars Store (x_0 Value_0) Stack-mapping_1 ...)
   (store-with-vars (store-with-var Store x_0 Value_0) Stack-mapping_1 ...)]

  )

(define-metafunction Dada
  ;; push-stack-segment
  ;;
  ;; Push a fresh stack segment onto the store
  push-stack-segment : Store -> Store
  [(push-stack-segment Store)
   (store-with-stack-segments Store ([] Stack-segment ...))
   (where/error (Stack-segment ...) (stack-segments-in-store Store))])

(define-metafunction Dada
  ;; pop-stack-segment
  ;;
  ;; Pops off the top-most stack segment and returns the values within,
  ;; along with a fresh store.
  pop-stack-segment : Store -> ((Value ...) Store)
  [(pop-stack-segment Store)
   ((Value ...) (store-with-stack-segments Store (Stack-segment_1 ...)))
   (where/error (((x Value) ...) Stack-segment_1 ...) (stack-segments-in-store Store))])

(define-metafunction Dada
  ;; store-with-updated-var
  ;;
  ;; Read the Value for a given variable from the stack.
  store-with-updated-var : Store x Value -> Store
  [(store-with-updated-var Store x Value)
   (store-with-stack-segments Store Stack-segments)
   (where/error Stack-segments (stack-segments-with-updated-var (stack-segments-in-store Store) x Value))])

(define-metafunction Dada
  ;; stack-segments-with-updated-var[(a 22) (b 44)]
  ;;
  ;; Read the Value for a given variable from the stack.
  stack-segments-with-updated-var : Stack-segments x Value -> Stack-segments

  [; Is the left-most variable named x?
   (stack-segments-with-updated-var (((x Value_0) Stack-mapping ...) Stack-segment ...) x Value_1)
   (((x Value_1) Stack-mapping ...) Stack-segment ...)]

  [; Else, drop the left-most variable
   (stack-segments-with-updated-var ((Stack-mapping_0 Stack-mapping_1 ...) Stack-segment ...) x Value)
   ((Stack-mapping_0 Stack-mapping_out ...) Stack-segment_out ...)
   (where/error ((Stack-mapping_out ...) Stack-segment_out ...) (stack-segments-with-updated-var ((Stack-mapping_1 ...) Stack-segment ...) x Value))]

  [; Drop the left-most segment, if it is empty
   (stack-segments-with-updated-var (() Stack-segment ...) x Value)
   (() Stack-segment_out ...)
   (where/error (Stack-segment_out ...) (stack-segments-with-updated-var (Stack-segment ...) x Value))]

  )

(module+ test
  (redex-let*
   Dada
   [(Store
     (term ([[(c 42) (a 66) (a 88) (d 11)] [(a 22) (b 44)]]
            []
            []
            )))]
   (test-equal-terms (var-in-store Store a) 66)
   (test-equal-terms (var-in-store Store b) 44)
   (test-equal-terms (var-in-store Store c) 42)
   (test-equal-terms (var-in-store Store d) 11)

   (test-equal-terms (stack-segments-in-store (store-with-var Store e 99))
                     [[(e 99) (c 42) (a 66) (a 88) (d 11)] [(a 22) (b 44)]])
   (test-equal-terms (stack-segments-in-store (store-with-var Store a 99))
                     [[(a 99) (c 42) (a 66) (a 88) (d 11)] [(a 22) (b 44)]])
   (test-equal-terms (stack-segments-in-store (store-with-vars Store (a 99) (e 98)))
                     [[(e 98) (a 99) (c 42) (a 66) (a 88) (d 11)] [(a 22) (b 44)]])

   (test-equal-terms (stack-segments-in-store (store-with-updated-var Store a 99))
                     [[(c 42) (a 99) (a 88) (d 11)] [(a 22) (b 44)]])
   (test-equal-terms (stack-segments-in-store (store-with-updated-var Store b 99))
                     [[(c 42) (a 66) (a 88) (d 11)] [(a 22) (b 99)]])
   (test-equal-terms (stack-segments-in-store (store-with-updated-var Store c 99))
                     [[(c 99) (a 66) (a 88) (d 11)] [(a 22) (b 44)]])
   (test-equal-terms (stack-segments-in-store (store-with-updated-var Store d 99))
                     [[(c 42) (a 66) (a 88) (d 99)] [(a 22) (b 44)]])

   (test-equal-terms (stack-segments-in-store (push-stack-segment Store))
                     [[] [(c 42) (a 66) (a 88) (d 11)] [(a 22) (b 44)]])

   (test-equal-terms (pop-stack-segment Store)
                     ([42 66 88 11] ([[(a 22) (b 44)]] [] [])))

   )
  )
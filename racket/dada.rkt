#lang racket
(require redex)
(require "grammar.rkt")
(require "opsem.rkt")
(require "type-system.rkt")

;; TODO
;;
;; * Generics
;; * ref classes/structs
;; * ref types
;; * interfaces and dyn types
;; * forall types
;; * existential types


;; random rules not to forget:
;;
;; - data cannot directly embed classes, or else we have to adjust is-affine-ty to walk data fields
;; -
#lang racket/base

(require (only-in "reduction.rkt"
                  ReduceM
                  define-reduction
                  inst-reduction
                  apply-reduction*))
(provide (all-from-out "reduction.rkt"))

(require "set.rkt")
(define set-∅ ∅)
(define set-∈ ∈)
(provide (all-from-out "set.rkt") set-∅ set-∈)

(require (rename-in "map.rkt" [∅ map-∅] [∈ map-∈]))
(provide (all-from-out "map.rkt"))

(module+ test
  (require (submod lightstep/reduction test))
  (require (submod lightstep/sample/unit-tests scope2))
  (require (submod lightstep/sample/design1 test))
  (require (submod lightstep/sample/design2 test))
  (require (submod lightstep/sample/design3 test))
  (require (submod lightstep/sample/design4 test))
  (require (submod lightstep/sample/design5 test))
  )

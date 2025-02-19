#lang racket

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

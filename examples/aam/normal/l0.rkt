#lang racket/base
(require lightstep/base lightstep/syntax)
(provide L₀ r₀ to-five r₁)

(module+ test (require rackunit))

;;-----------------------------------------------------------------------------
;; 3.5 A brief aside on the caveats of language extensions

(define-language L₀
  [M ∷= (? number?)])
(define-reduction (r₀)
  [M 5])
(define step-r₀ (call-with-values (λ () (r₀)) compose1))

(module+ test
  (check-equal? (step-r₀ 7) (set 5)))

(define (to-five m)
  (match m
    [M 5]))
(define-reduction (r₁)
  [M (to-five M)])
(define step-r₁ (call-with-values (λ () (r₁)) compose1))

(module+ test
  (check-equal? (step-r₁ 7) (set 5)))

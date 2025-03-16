#lang racket/base
(require lightstep/base lightstep/syntax lightstep/inference)
(provide L₀ r₀-rule to-five r₁-rule)

(module+ test (require rackunit))

;;-----------------------------------------------------------------------------
;; 3.5 A brief aside on the caveats of language extensions

(define-language L₀
  [M ∷= (? number?)])
(define-inference (r₀-rule)
  [---------
   `(,M → 5)])
(define r₀ (call-with-values (λ () (r₀-rule)) compose1))

(module+ test
  (check-equal? (r₀ 7) (set 5)))

(define/match (to-five m)
  [M 5])
(define-inference (r₁-rule)
  [--------------------
   `(,M → ,(to-five M))])
(define r₁ (call-with-values (λ () (r₁-rule)) compose1))

(module+ test
  (check-equal? (r₁ 7) (set 5)))

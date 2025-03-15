#lang racket/base
(require lightstep/base lightstep/syntax
         (only-in "l0.rkt" L₀ r₀ r₁ to-five))

(module+ test (require rackunit))

;;-----------------------------------------------------------------------------
;; 3.5 A brief aside on the caveats of language extensions

(define-language L₁ #:super L₀
  [M ∷= .... (? string?)])

(module+ test
  (check-true (M? 5))
  (check-true (M? "five")))

(define-reduction (r₀′) #:super [(r₀)])
(define step-r₀′ (call-with-values (λ () (r₀′)) compose1))

(module+ test
  (check-equal? (step-r₀′ "seven") (set 5)))

(define-reduction (r₁′) #:super [(r₁)])
(define step-r₁′ (call-with-values (λ () (r₁′)) compose1))

(module+ test
  (check-exn #rx"no matching clause" (λ () (step-r₁′ "seven"))))

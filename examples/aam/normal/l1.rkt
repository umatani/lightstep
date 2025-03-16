#lang racket/base
(require lightstep/base lightstep/syntax lightstep/inference
         (only-in "l0.rkt" L₀ r₀-rule r₁-rule [to-five L₀:to-five]))

(module+ test (require rackunit))

;;-----------------------------------------------------------------------------
;; 3.5 A brief aside on the caveats of language extensions

(define-language L₁ #:super L₀
  [M ∷= .... (? string?)])

(module+ test
  (check-true (M? 5))
  (check-true (M? "five")))

(define-inference (r₀′-rule) #:super [(r₀-rule)])
(define r₀′ (call-with-values (λ () (r₀′-rule)) compose1))

(module+ test
  (check-equal? (r₀′ "seven") (set 5)))

;; Redex cannot do as follows

(define/match (to-five m) #:super L₀:to-five)
(define-reduction (r₁′-rule) #:super [(r₁-rule)])
(define r₁′ (call-with-values (λ () (r₁′-rule)) compose1))

(module+ test
  (check-equal? (r₁′ "seven") (set 5)))

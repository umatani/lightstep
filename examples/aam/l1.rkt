#lang racket/base
(require lightstep/base lightstep/syntax
         (only-in racket/unit invoke-unit)
         "l0.rkt")

(module+ test (require rackunit))

;; Abstracting Abstract Machines from:
;;   https://dvanhorn.github.io/redex-aam-tutorial/

;;-----------------------------------------------------------------------------
;; 3.5 A brief aside on the caveats of language extensions

(define-language L₁ #:super L₀
  [M ∷= .... (? string?)])

(module+ test
  (check-true (M? 5))
  (check-true (M? "five")))

(define-reduction (r₀′-rules) #:super [(r₀-rules)])
(define r₀′ (call-with-values
             (λ () (invoke-unit (r₀′-rules)))
             compose1))

(module+ test
  (check-equal? (r₀′ "seven") (set 5)))

(define-reduction (r₁′-rules) #:super [(r₁-rules)])
(define r₁′ (call-with-values
             (λ () (invoke-unit (r₁′-rules)))
             compose1))

(module+ test
  (check-exn #rx"no matching clause" (λ () (r₁′ "seven"))))

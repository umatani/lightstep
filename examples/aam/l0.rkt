#lang racket/base
(require lightstep/base lightstep/syntax)
(provide L₀ r₀-rules to-five r₁-rules)

(module+ test (require rackunit))

;; Abstracting Abstract Machines from:
;;   https://dvanhorn.github.io/redex-aam-tutorial/

;;-----------------------------------------------------------------------------
;; 3.5 A brief aside on the caveats of language extensions

(define-language L₀
  [M ∷= (? number?)])
(define-reduction (r₀-rules)
  [M 5])
(define r₀ (call-with-values
            (λ () (r₀-rules))
            compose1))

(module+ test
  (check-equal? (r₀ 7) (set 5)))

(define (to-five m)
  (match m
    [M 5]))
(define-reduction (r₁-rules)
  [M (to-five M)])
(define r₁ (call-with-values
            (λ () (r₁-rules))
            compose1))

(module+ test
  (check-equal? (r₁ 7) (set 5)))

#lang racket/base
(require lightstep/base
         (prefix-in lam: (only-in "lam.rkt" FV FV-info)))


(module+ test (require rackunit))

;;=============================================================================
;; 4.1 ISWIM Expressions

(define-syntax-rule (define-iswim-language L r ...)
  (define-language L
    [M ∷=
       X
       `(λ ,X ,M)
       `(,M₁ ,M₂)
       (? b?)
       `(,(? oⁿ?) ,M (... ...))]
    [X ∷= (? symbol? (not 'λ))]
    r ...))

(define-iswim-language ISWIM
  [b ∷= (? number?)]
  [oⁿ ∷= (? o¹?) (? o²?)]
  [o¹ ∷= 'add1 'sub1 'iszero]
  [o² ∷= '+ '- '* '↑])

(module+ test
  (check-true  (M? 1))
  (check-true  (M? '(↑ 1 2)))
  (check-false (M? '(/ 1 2))))

(define/match (FV m) #:super lam:FV
  [(? b?) ∅]
  [`(,(? oⁿ?) ,M ...)
   (apply ∪ (map FV M))])

(module+ test
  (check-equal? (FV 'x)               (set 'x))
  (check-equal? (FV '(x (y x)))       (set 'x 'y))
  (check-equal? (FV '(λ x (x y)))     (set 'y))
  (check-equal? (FV '(z (λ z z)))     (set 'z))
  (check-equal? (FV 123)              ∅)
  (check-equal? (FV '(↑ (f x) (g 1))) (set 'f 'x 'g)))

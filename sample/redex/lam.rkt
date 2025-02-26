#lang racket
(require lightstep/base)

(module+ test (require rackunit))

(define-language LAM
  [M ∷=
     X
     `(λ ,X ,M)
     `(,M₁ ,M₂)]
  [X ∷= (? symbol? (not 'λ))])

(module+ test
  (check-true (M? 'x))
  (check-true (M? '(x y)))
  (check-true (M? '(λ x x)))
  (check-true (M? '((x y) (z w))))
  (check-true (M? '(λ y (λ z y))))
  (check-true (M? '((λ y (y y)) (λ y (y y))))))

(define (FV m)
  (match m
    [X          (set X)]
    [`(λ ,X ,M) (set-remove (FV M) X)]
    [`(,M₁ ,M₂) (∪ (FV M₁) (FV M₂))]))

(module+ test
  (check-equal? (FV 'x)           (set 'x))
  (check-equal? (FV '(x (y x)))   (set 'x 'y))
  (check-equal? (FV '(λ x (x y))) (set 'y))
  (check-equal? (FV '(z (λ z z))) (set 'z)))

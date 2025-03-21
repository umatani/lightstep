#lang racket/base
(require "match.rkt")
(provide zipWith zip unzip)

(module+ test (require rackunit))

;;=============================================================================
;; Miscellaneous utilities

;; (α β → γ) → List(α) List(β) → List(γ)
(define ((zipWith f) as bs)
  (define/match (go as bs)
    [('() _  ) '()]
    [(_   '()) '()]
    [(`(,a ,as ...) `(,b ,bs ...)) (cons (f a b) (go as bs))])
  (go as bs))

;; List(α) List(β) → List([α . β])
(define zip  (zipWith cons))

;; List([α . β]) → [List(α) . List(β)]
(define (unzip abs)
  (foldr (λ (ab abs) (match* (ab abs)
                       [(`(,a . ,b) `(,as . ,bs))
                        `(,(cons a as) . ,(cons b bs))]))
         (cons '() '()) abs))


(module+ test
  (define abs '([a . 1] [b . 2] [c . 3]))
  (check-equal? (match (unzip abs) [`(,as . ,bs) (zip as bs)]) abs))

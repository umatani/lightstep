#lang racket
(require lightstep/base
         (only-in "design1.rkt" val?)
         (only-in "design3.rkt" subst EC)
         (reduction-in "design3.rkt" -->PCF₅-rule))

(module+ test (require rackunit))

;;;; parameter化の利点(つづき)：ambの意味を
;;;; randomization から nondeterministic computation へ

;; selectの置き換え， ≔<2> を ← に．
(define select list→set)

(define-reduction (-->PCF₆-rule --> ≔<1> ≔<2>)
  #:super (-->PCF₅-rule --> ≔<1> ≔<2>))

(define-values (-->PCF₆ reducer-PCF₆)
  (call-with-values
   (λ () (invoke-unit (-->PCF₆-rule reducer-PCF₆ ≔ ←)))
   (λ (mrun reducer) (values (compose1 mrun reducer) reducer))))
(define -->>PCF₆ (repeated -->PCF₆))

(module+ test
  (printf "----- PCF6 ------------\n")
  (check-equal? (car (-->>PCF₆ '(amb 1 2 3 4 5)))
                (set 1 2 3 4 5))
  (check-equal? (car (-->>PCF₆ '(+ (amb 1 2 3 4) (amb 10 20 30 40))))
                (set 32 33 34 21 22 23 24 41 42 13 14 31 11 43 12 44)))

;; define-reduction時に ≔<1>, ≔<2>を固定できることも可能

(define-reduction (-->PCF₆-v2-rule -->)
  #:super (-->PCF₅-rule --> ≔ ←))

(define-values (-->PCF₆-v2 reducer-PCF₆-v2)
  (call-with-values
   (λ () (invoke-unit (-->PCF₆-v2-rule reducer-PCF₆-v2)))
   (λ (mrun reducer) (values (compose1 mrun reducer) reducer))))
(define -->>PCF₆-v2 (repeated -->PCF₆-v2))

(module+ test
  (printf "----- PCF6-v2 ------------\n")
  (check-equal? (car (-->>PCF₆-v2 '(amb 1 2 3 4 5)))
                (set 1 2 3 4 5))
  (check-equal? (car (-->>PCF₆-v2 '(+ (amb 1 2 3 4) (amb 10 20 30 40))))
                (set 32 33 34 21 22 23 24 41 42 13 14 31 11 43 12 44)))

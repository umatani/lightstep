#lang racket
(require lightstep/reduction lightstep/set
         (only-in "design1.rkt" val?)
         (only-in "design3.rkt" subst EC -->PCF₅-rule))

(module+ test (require rackunit))

;;;; parameter化の利点(つづき)：ambの意味を
;;;; randomization から nondeterministic computation へ

;; selectの置き換え， ≔<2> を ← に．
(define select list→set)

(define-reduction (-->PCF₆-rule --> ≔<1> ≔<2>)
  #:super (-->PCF₅-rule --> ≔<1> ≔<2>))

(define -->PCF₆ (invoke-unit (inst-reduction -->PCF₆-rule -->PCF₆ ≔ ←)))

(module+ test
  ;;(printf "----- PCF6 ------------\n")
  (check-equal? (car (apply-reduction* -->PCF₆ '(amb 1 2 3 4 5)))
                (set 1 2 3 4 5))
  (check-equal? (car (apply-reduction* -->PCF₆
                                       '(+ (amb 1 2 3 4)
                                           (amb 10 20 30 40))))
                (set 32 33 34 21 22 23 24 41 42 13 14 31 11 43 12 44)))

;; define-reduction時に ≔<1>, ≔<2>を固定できることも可能

(define-reduction (-->PCF₆-v2-rule -->)
  #:super (-->PCF₅-rule --> ≔ ←))

(define -->PCF₆-v2 (invoke-unit (inst-reduction -->PCF₆-v2-rule -->PCF₆-v2)))

(module+ test
  ;;(printf "----- PCF6-v2 ------------\n")
  (check-equal? (car (apply-reduction* -->PCF₆-v2 '(amb 1 2 3 4 5)))
                (set 1 2 3 4 5))
  (check-equal? (car (apply-reduction* -->PCF₆-v2
                                       '(+ (amb 1 2 3 4)
                                           (amb 10 20 30 40))))
                (set 32 33 34 21 22 23 24 41 42 13 14 31 11 43 12 44)))

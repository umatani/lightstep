#lang racket
(require lightstep/base lightstep/syntax lightstep/inference
         (only-in "design05.rkt" PCF₅ subst E -->PCF₅))

(module+ test (require rackunit))

;;;; parameter化の利点(つづき)：ambの意味を
;;;; randomization から nondeterministic computation へ

;; 言語定義のインポート
(define-language PCF₆ #:super PCF₅)

;; selectの置き換え， ≔<2> を ← に．
(define select list→set)

(define-inference (-->PCF₆ ≔<1> ≔<2>) #:super [(-->PCF₅ ≔<1> ≔<2>)])


(define step-->PCF₆ (call-with-values (λ () (-->PCF₆ ≔ ←)) compose1))
(define -->>PCF₆ (compose1 car (repeated step-->PCF₆)))

(module+ test
  ;(printf "----- PCF₆ ------------\n")
  (check-equal? (-->>PCF₆ '(amb 1 2 3 4 5))
                (set 1 2 3 4 5))
  (check-equal? (-->>PCF₆ '(+ (amb 1 2 3 4) (amb 10 20 30 40)))
                (set 32 33 34 21 22 23 24 41 42 13 14 31 11 43 12 44)))

;; define-reduction時に ≔<1>, ≔<2>を固定することも可能

(define-inference (-->PCF₆-v2) #:super [(-->PCF₅ ≔ ←)])

(define step-->PCF₆-v2 (call-with-values (λ () (-->PCF₆-v2)) compose1))
(define -->>PCF₆-v2 (compose1 car (repeated step-->PCF₆-v2)))

(module+ test
  ;(printf "----- PCF₆-v2 ------------\n")
  (check-equal? (-->>PCF₆-v2 '(amb 1 2 3 4 5))
                (set 1 2 3 4 5))
  (check-equal? (-->>PCF₆-v2 '(+ (amb 1 2 3 4) (amb 10 20 30 40)))
                (set 32 33 34 21 22 23 24 41 42 13 14 31 11 43 12 44)))

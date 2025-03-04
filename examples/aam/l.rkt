#lang racket/base
(require lightstep/base lightstep/syntax
         (only-in "common.rkt" match?))

(module+ test (require rackunit))

;; Abstracting Abstract Machines from:
;;   https://dvanhorn.github.io/redex-aam-tutorial/

;;=============================================================================
;; 2 Warmup

(module+ test (require rackunit))

(define-language L
  [M ∷= N F `(,M ...)]
  [F ∷= 'fred 'wilma]
  [N ∷= 2 7])

(module+ test
  (check-true  (N? 2))
  (check-false (N? 9))
  (check-false (N? 'fred))
  (check-true  (M? '(((((((fred)))))))))

  (check-false (match? `(,N ...) 2))
  (check-true  (match? `(,N ...) '(7 2 7)))
  (check-false (match? `(,M ,M) '(7 (2 fred))))
  (check-true  (match? `(,M ,M) '((2 fred) (2 fred))))
  (check-true  (match? `(,M ,M ,M) '((2 fred) (2 fred) (2 fred))))
  (check-true  (match? `(,M₁ ,M₂) '(7 (2 fred))))

  (check-false (match? (and `(,M ,M)
                            (app (match-λ [`(,m₁ ,m₂) (equal? m₁ m₂)]) #t))
                       '(7 (2 fred))))
  (check-true (match? (and `(,M ,M)
                           (app (match-λ [`(,m₁ ,m₂) (equal? m₁ m₂)]) #t))
                      '((2 fred) (2 fred)))))

(define (swap M)
  (match M
    ['fred 'wilma]
    ['wilma 'fred]
    [`(,M ...) (map swap M)]
    [M M]))

(module+ test
  (check-equal? (swap '(wilma fred)) '(fred wilma))
  (check-equal? `(7 ,(swap '(wilma 2 (fred)))) '(7 (fred 2 (wilma)))))

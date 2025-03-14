#lang racket/base
(require lightstep/base lightstep/syntax
         (only-in "iswim.rkt" FV δ)
         (only-in "secd.rkt" SECD mkSECD)
         (only-in "secd-tco.rkt" ⊢->secd/tco))

(module+ test (require rackunit))

;;=============================================================================
;; Exercise 7.7  SECD with TCO (Tail Call Optimization) and SS (Safe for Space)

(define-language SECD/TCO/SS #:super SECD)

(define-reduction (⊢->secd/tco/ss) #:super [(⊢->secd/tco)]
  [`((λ ,X ,M) ,C ...)
   S ← get-S
   E ← get-E
   (put-S (cons `((λ ,X ,M) ,(restrict E (FV `(λ ,X ,M)))) S))
   `(,@C)
   "secd4"])

(define step⊢->secd/tco/ss (let-values ([(mrun reducer) (⊢->secd/tco/ss)])
                             (match-λ
                              [(mkSECD S E Cs D)
                               (mrun D E S (reducer Cs))])))
(define ⊢->>secd/tco/ss (compose1 car (repeated step⊢->secd/tco/ss)))

(define/match (evalsecd/tco/ss m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>secd/tco/ss (mkSECD '() (↦) `(,M) 'ϵ))
     [(set (mkSECD `(,(? b? b)) E '() 'ϵ))
      b]
     [(set (mkSECD `(((λ ,X ,M) ,E′)) E '() 'ϵ))
      'function]
     [x (error 'evalsecd/tco/ss "invalid final state: ~a" x)])]
  [_ (error 'evalsecd/tco/ss "invalid input: ~a" m)])

(module+ test
  (require (only-in (submod "cc.rkt" test) Ω))

  (check-equal? (⊢->>secd/tco/ss (mkSECD
                                  '()
                                  (↦ ['x 1])
                                  '((- (↑ 10 2) (* (add1 4) (+ x 2))))
                                  'ϵ))
                (set (mkSECD '(85) (↦ ['x 1]) '() 'ϵ)))
  (check-equal? (⊢->>secd/tco/ss (mkSECD
                                  '()
                                  (↦ ['x 1])
                                  '(((λ x (+ x x)) (add1 x)))
                                  'ϵ))
                (set (mkSECD '(4) (↦ ['x 2]) '() 'ϵ)))

  (check-equal? (evalsecd/tco/ss '(- (↑ 10 2) (* (add1 4) (+ 1 2)))) 85)
  (check-equal? (evalsecd/tco/ss '((λ x (+ x x)) (add1 1))) 4)

  (check-equal? (evalsecd/tco/ss '(+ (* 9 (↑ 2 3)) 3)) 75)
  (check-equal? (evalsecd/tco/ss '(((λ f (λ x (f x))) (λ y (+ y y))) 8)) 16)

  (check-equal? (⊢->>secd/tco/ss (mkSECD '() (↦) `(,Ω) 'ϵ)) ∅))

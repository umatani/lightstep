#lang racket/base
(require lightstep/base lightstep/syntax
         (only-in racket/unit)
         (only-in "iswim.rkt" FV δ)
         (only-in "secd.rkt" SECD ⊢->secd-rules mkSECD))
(provide ⊢->secd/tco-rules)

(module+ test (require rackunit))

;;=============================================================================
;; Exercise 7.4  SECD machine with TCO (Tail Call Optimization)

(define-language SECD/TCO #:super SECD)

(define-reduction (⊢->secd/tco-rules) #:super [(⊢->secd-rules)]

  [`((ap) ,C₁ ,C ...)
   `(,V ((λ ,X ,M) ,E′) ,V′ ...) ← get-S
   E ← get-E
   D ← get-D
   (put-S '())
   (put-E (E′ X V))
   (put-D `((,@V′) ,E (,C₁ ,@C) ,D))
   `(,M)
   "secd5"]

  [`((ap))
   `(,V ((λ ,X ,M) ,E′)) ← get-S
   (put-S '())
   (put-E (E′ X V))
   `(,M)
   "secd5-tc"])

(define ⊢->secd/tco (call-with-values
                     (λ () (⊢->secd/tco-rules))
                     (λ (mrun reducer)
                       (λ (ς)
                         (match ς
                           [(mkSECD S E Cs D)
                            (mrun D E S (reducer Cs))])))))
(define ⊢->>secd/tco (compose1 car (repeated ⊢->secd/tco)))

(define/match (evalsecd/tco m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>secd/tco (mkSECD '() (↦) `(,M) 'ϵ))
     [(set (mkSECD `(,(? b? b)) E '() 'ϵ))
      b]
     [(set (mkSECD `(((λ ,X ,M) ,E′)) E '() 'ϵ))
      'function]
     [x (error 'evalsecd/tco "invalid final state: ~a" x)])]
  [_ (error 'evalsecd/tco "invalid input: ~a" m)])

(module+ test
  (require (only-in (submod "cc.rkt" test) Ω))

  (check-equal? (⊢->>secd/tco (mkSECD
                               '()
                               (↦ ['x 1])
                               '((- (↑ 10 2) (* (add1 4) (+ x 2))))
                               'ϵ))
                (set (mkSECD '(85) (↦ ['x 1]) '() 'ϵ)))
  (check-equal? (⊢->>secd/tco (mkSECD
                               '()
                               (↦ ['x 1])
                               '(((λ x (+ x x)) (add1 x)))
                               'ϵ))
                (set (mkSECD '(4) (↦ ['x 2]) '() 'ϵ)))

  (check-equal? (evalsecd/tco '(- (↑ 10 2) (* (add1 4) (+ 1 2)))) 85)
  (check-equal? (evalsecd/tco '((λ x (+ x x)) (add1 1))) 4)

  (check-equal? (evalsecd/tco '(+ (* 9 (↑ 2 3)) 3)) 75)
  (check-equal? (evalsecd/tco '(((λ f (λ x (f x))) (λ y (+ y y))) 8)) 16)

  (check-equal? (⊢->>secd/tco (mkSECD '() (↦) `(,Ω) 'ϵ)) ∅))

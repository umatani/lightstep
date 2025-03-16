#lang racket/base
(require lightstep/base lightstep/syntax
         (only-in racket/unit)
         (only-in "iswim.rkt" FV δ)
         (only-in "secd.rkt" SECD ⊢->secd mkSECD))
(provide ⊢->secd/tco)

(module+ test (require rackunit))

;;=============================================================================
;; Exercise 7.4  SECD machine with TCO (Tail Call Optimization)

(define-language SECD/TCO #:super SECD)

(define-reduction (⊢->secd/tco) #:super [(⊢->secd)]
  [`(((ap) ,C₁ ,C ...) ,E)
   `(,V ((λ ,X ,M) ,E′) ,V′ ...) ← get-S
   (put-S '())
   D ← get-D
   (put-D `((,@V′) ,E (,C₁ ,@C) ,D))
   `((,M) ,(E′ X V))
   "secd5"]

  [`(((ap)) ,E)
   `(,V ((λ ,X ,M) ,E′)) ← get-S
   (put-S '())
   `((,M) ,(E′ X V))
   "secd5-tc"])

(define step⊢->secd/tco (let-values ([(mrun reducer) (⊢->secd/tco)])
                          (match-λ
                           [(mkSECD S E Cs D)
                            (mrun D S (reducer `(,Cs ,E)))])))
(define ⊢->>secd/tco (compose1 car (repeated step⊢->secd/tco)))

(define/match (evalsecd/tco m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>secd/tco (mkSECD '() (↦) `(,M) 'ϵ))
     [(set (mkSECD `(,(? b? b)) E '() 'ϵ))
      b]
     [(set (mkSECD `(((λ ,X ,M) ,E′)) E '() 'ϵ))
      'function]
     [x (error 'evalsecd/tco "invalid final state: ~s" x)])]
  [_ (error 'evalsecd/tco "invalid input: ~s" m)])

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

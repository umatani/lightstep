#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/transformers
         lightstep/inference
         (only-in racket/list append-map)
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" FV δ)
         (only-in "secd.rkt" SECD  ⊢->secd-rules mkSECD))

(module+ test (require rackunit))

;;=============================================================================
;; Exercise 7.1  SECD machine with byte-code compiler

(define-language SECD₂ #:super SECD
  [C ∷= '(ap) `(prim ,(? oⁿ?)) (? b? b) X `(,X (,C ...))]
  [V ∷= (? b?) `((λ ,X (,C ...)) ,E)])

(define-inference (⊢->secd₂-rules) #:super [(⊢->secd-rules)]

  [(error "no such case")
   --------------------------------------------------------- "secdPA"
   `((((,(? oⁿ? oⁿ) ,M ...) ,C ...) ,E) → (,(void) ,(void)))         ]

  [(error "no such case")
   --------------------------------------------------------- "secdLA"
   `((((,M₁ ,M₂)            ,C ...) ,E) → (,(void) ,(void)))         ]

  [S ← get-S
   (put-S (cons `((λ ,X (,@C′)) ,E) S))
   -------------------------------------------- "secd4"
   `((((,X (,C′ ...)) ,C ...) ,E) → ((,@C) ,E))        ]

  [`(,V ((λ ,X (,C′ ...)) ,E′) ,V′ ...) ← get-S
   (put-S '())
   D ← get-D
   (put-D `((,@V′) ,E (,@C) ,D))
   -------------------------------------------- "secd5"
   `((((ap) ,C ...) ,E) → ((,@C′) ,(E′ X V)))          ])

(define ⊢->secd₂ (let-values ([(mrun reducer) (⊢->secd₂-rules)])
                   (match-λ
                    [(mkSECD S E Cs D)
                     (mrun D S (reducer `(,Cs ,E)))])))
(define ⊢->>secd₂ (compose1 car (repeated ⊢->secd₂)))

(define/match (compile m)
  [X
   `(,X)]

  [`(λ ,X ,M)
   `((,X ,(compile M)))]

  [`(,M₁ ,M₂)
   `(,@(compile M₁) ,@(compile M₂) (ap))]

  [(? b? b)
   `(,b)]

  [`(,(? oⁿ? oⁿ) ,M ...)
   `(,@(append-map compile M) (prim ,oⁿ))])

(define/match (evalsecd₂ m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>secd₂ (mkSECD '() (↦) (compile M) 'ϵ))
     [(set (mkSECD `(,(? b? b)) E '() 'ϵ))
      b]
     [(set (mkSECD `(((λ ,X (,C ...)) ,E′)) E '() 'ϵ))
      'function]
     [x (error 'evalsecd₂ "invalid final state: ~s" x)])]
  [_ (error 'evalsecd₂ "invalid input: ~s" m)])

(module+ test
  (require (only-in (submod "cc.rkt" test) Ω))

  (check-equal? (⊢->>secd₂ (mkSECD
                            '()
                            (↦ ['x 1])
                            (compile '(- (↑ 10 2) (* (add1 4) (+ x 2))))
                            'ϵ))
                (set (mkSECD '(85) (↦ ['x 1]) '() 'ϵ)))
  (check-equal? (⊢->>secd₂ (mkSECD
                            '()
                            (↦ ['x 1])
                            (compile '((λ x (+ x x)) (add1 x)))
                            'ϵ))
                (set (mkSECD '(4) (↦ ['x 1]) '() 'ϵ)))

  (check-equal? (evalsecd₂ '(- (↑ 10 2) (* (add1 4) (+ 1 2)))) 85)
  (check-equal? (evalsecd₂ '((λ x (+ x x)) (add1 1))) 4)

  (check-equal? (evalsecd₂ '(+ (* 9 (↑ 2 3)) 3)) 75)
  (check-equal? (evalsecd₂ '(((λ f (λ x (f x))) (λ y (+ y y))) 8)) 16)

  ;; loops forever
  ;; (⊢->>secd₂ (mkSECD '() (↦) (compile Ω) 'ϵ))
  )

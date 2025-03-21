#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/transformers
         (only-in racket/list append-map)
         (only-in "iswim.rkt" FV δ)
         (only-in "secd.rkt" SECD  ⊢->secd mkSECD))

(module+ test (require rackunit))

;;=============================================================================
;; Exercise 7.1  SECD machine with byte-code compiler

(define-language SECD₂ #:super SECD
  [C ∷= '(ap) `(prim ,(? oⁿ?)) (? b? b) X `(,X (,C ...))]
  [V ∷= (? b?) `((λ ,X (,C ...)) ,E)])

;; (((C ...) E) S D) --> (((C ...) E) S D)
(define-reduction (⊢->secd₂) #:super [(⊢->secd)]

  [`(((,(? oⁿ? oⁿ) ,M ...) ,C ...) ,E) (error "no such case") "secdPA"]
  [`(((,M₁ ,M₂)            ,C ...) ,E) (error "no such case") "secdLA"]

  [`(((,X (,C′ ...)) ,C ...) ,E)
   S ← get-S
   (put-S (cons `((λ ,X (,@C′)) ,E) S))
   `((,@C) ,E)
   "secd4"]

  [`(((ap) ,C ...) ,E)
   `(,V ((λ ,X (,C′ ...)) ,E′) ,V′ ...) ← get-S
   (put-S '())
   D ← get-D
   (put-D `((,@V′) ,E (,@C) ,D))
   `((,@C′) ,(E′ X V))
   "secd5"])

;; (((C ...) E) S D) → 𝒫((((C ...) E) S D))
(define step⊢->secd₂ (let-values ([(mrun reducer) (⊢->secd₂)])
                       (match-λ
                        [(mkSECD S E Cs D)
                         (mrun D S (reducer `(,Cs ,E)))])))
(define ⊢->>secd₂ (compose1 car (repeated step⊢->secd₂)))

;; M → (C ...)
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

;; M → V
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

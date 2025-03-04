#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/transformers
         (only-in racket/unit invoke-unit)
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

(define-reduction (⊢->secd₂-rules) #:super [(⊢->secd-rules)]

  [`((,(? oⁿ? oⁿ) ,M ...) ,C ...) (error "no such case") "secdPA"]
  [`((,M₁ ,M₂)            ,C ...) (error "no such case") "secdLA"]

  [`((,X (,C′ ...)) ,C ...)
   S ← get-S
   E ← get-E
   (put-S (cons `((λ ,X (,@C′)) ,E) S))
   `(,@C)
   "secd4"]

  [`((ap) ,C ...)
   `(,V ((λ ,X (,C′ ...)) ,E′) ,V′ ...) ← get-S
   E ← get-E
   D ← get-D
   (put-S '())
   (put-E (E′ X V))
   (put-D `((,@V′) ,E (,@C) ,D))
   `(,@C′)
   "secd5"])

(define ⊢->secd₂ (call-with-values
                  (λ () (invoke-unit (⊢->secd₂-rules)))
                  (λ (mrun reducer)
                    (λ (ς)
                      (match ς
                        [(mkSECD S E Cs D)
                         (mrun D E S (reducer Cs))])))))
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
     [x (error 'evalsecd₂ "invalid final state: ~a" x)])]
  [_ (error 'evalsecd₂ "invalid input: ~a" m)])

(module+ test
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
  (check-equal? (evalsecd₂ '(((λ f (λ x (f x))) (λ y (+ y y))) 8)) 16))

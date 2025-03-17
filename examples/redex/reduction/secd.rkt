#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/transformers
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" ISWIM FV δ))
(provide SECD ⊢->secd mkSECD)

(module+ test (require rackunit))

;;=============================================================================
;; 7 Tail Cals and More Space Savings

(define-language SECD #:super ISWIM
  [S ∷= (? list? Vs)]
  [E ∷= (? map? X→V)]
  [C ∷= '(ap) `(prim ,(? oⁿ?)) M]
  [D ∷= 'ϵ `(,S ,E ,(? list? Cs) ,D)]
  [V ∷= (? b?) `((λ ,X ,M) ,E)])

;; (((C ...) E) S D) --> (((C ...) E) S D)
(define-reduction (⊢->secd)
  #:monad (StateT #f (StateT #f (NondetT ID)))
  #:do [(define get-S (bind get (compose1 return car)))
        (define get-D (bind get (compose1 return cdr)))
        (define (put-S S)
          (do `(,_ . ,D) ← get
              (put `(,S . ,D))))
        (define (put-D D)
          (do `(,S . ,_) ← get
              (put `(,S . ,D))))

        (define/match (apply-δ oⁿ S)
          [((or 'add1 'sub1 'iszero) `(,(? b? b) ,V ...))
           `(,(δ oⁿ `(,b)) ,@V)]
          [((or '+ '- '* '↑) `(,(? b? b₂) ,(? b? b₁) ,V ...))
           `(,(δ oⁿ `(,b₁ ,b₂)) ,@V)]
          [(_ _) (error 'apply-δ "failed: ~s ~s" oⁿ S)])]

  [`((,(? b? b) ,C ...) ,E)
   S ← get-S
   (put-S (cons b S))
   `((,@C) ,E)
   "secd1"]

  [`((,(? X? x) ,C ...) ,E)
   (↦ [x V]) ≔ E
   S ← get-S
   (put-S (cons V S))
   `((,@C) ,E)
   "secd2"]

  [`(((,(? oⁿ? oⁿ) ,M ...) ,C ...) ,E)
   `((,@M (prim ,oⁿ) ,@C) ,E)
   "secdPA"]

  [`(((prim ,(? oⁿ? oⁿ)) ,C ...) ,E)
   S ← get-S
   (put-S (apply-δ oⁿ S))
   `((,@C) ,E)
   "secd3"]

  [`(((,M₁ ,M₂) ,C ...) ,E)
   `((,M₁ ,M₂ (ap) ,@C) ,E)
   "secdLA"]

  [`(((λ ,X ,M) ,C ...) ,E)
   S ← get-S
   (put-S (cons `((λ ,X ,M) ,E) S))
   `((,@C) ,E)
   "secd4"]

  [`(((ap) ,C ...) ,E)
   `(,V ((λ ,X ,M) ,E′) ,V′ ...) ← get-S
   (put-S '())
   D ← get-D
   (put-D `((,@V′) ,E (,@C) ,D))
   `((,M) ,(E′ X V))
   "secd5"]

  [`(() ,E)
   `(,V ,V′ ...) ← get-S
   `(,S′ ,E′ (,C′ ...) ,D) ← get-D
   (put-S (cons V S′))
   (put-D D)
   `((,@C′) ,E′)
   "secd6"])

(define-match-expander mkSECD
  (syntax-parser
    [(_ S E Cs D)
     #'(cons (cons `(,Cs ,E) S) D)])
  (syntax-parser
    [(_ S E Cs D)
     #'(cons (cons `(,Cs ,E) S) D)]))

;; (((C ...) E) S D) → 𝒫((((C ...) E) S D))
(define step⊢->secd (let-values ([(mrun reducer) (⊢->secd)])
                      (match-λ
                       [(mkSECD S E Cs D)
                        (mrun D S (reducer `(,Cs ,E)))])))
(define ⊢->>secd (compose1 car (repeated step⊢->secd)))

;; M → V
(define/match (evalsecd m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>secd (mkSECD '() (↦) `(,M) 'ϵ))
     [(set (mkSECD `(,(? b? b)) E '() 'ϵ))
      b]
     [(set (mkSECD `(((λ ,X ,M) ,E′)) E '() 'ϵ))
      'function]
     [x (error 'evalsecd "invalid final state: ~s" x)])]
  [_ (error 'evalsecd "invalid input: ~s" m)])

(module+ test
  (require (only-in (submod "cc.rkt" test) Ω))

  (check-equal? (⊢->>secd (mkSECD '() (↦ ['x 1])
                                  '((- (↑ 10 2) (* (add1 4) (+ x 2)))) 'ϵ))
                (set (mkSECD '(85) (↦ ['x 1]) '() 'ϵ)))
  (check-equal? (⊢->>secd (mkSECD '() (↦ ['x 1])
                                  '(((λ x (+ x x)) (add1 x))) 'ϵ))
                (set (mkSECD '(4) (↦ ['x 1]) '() 'ϵ)))
  (check-equal? (evalsecd '(- (↑ 10 2) (* (add1 4) (+ 1 2)))) 85)
  (check-equal? (evalsecd '((λ x (+ x x)) (add1 1))) 4)

  (check-equal? (evalsecd '(+ (* 9 (↑ 2 3)) 3)) 75)
  (check-equal? (evalsecd '(((λ f (λ x (f x))) (λ y (+ y y))) 8)) 16)

  ;; loops forever
  ;; (⊢->>secd (mkSECD '() (↦) `(,Ω) 'ϵ))
  )

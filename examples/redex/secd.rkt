#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/transformers
         (only-in racket/unit invoke-unit)
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" ISWIM FV δ))
(provide SECD ⊢->secd-rules mkSECD)

(module+ test (require rackunit))

;;=============================================================================
;; 7 Tail Cals and More Space Savings

(define-language SECD #:super ISWIM
  [S ∷= (? list? Vs)]
  [E ∷= (? map? X→V)]
  [C ∷= '(ap) `(prim ,(? oⁿ?)) M]
  [D ∷= 'ϵ `(,S ,E ,(? list? Cs) ,D)]
  [V ∷= (? b?) `((λ ,X ,M) ,E)])

(define-reduction (⊢->secd-rules)
  #:monad (StateT #f (StateT #f (StateT #f (NondetT ID))))
  #:do [(define get-S (bind get (compose1 return car)))
        (define get-E (bind get (compose1 return cadr)))
        (define get-D (bind get (compose1 return cddr)))
        (define (put-S S)
          (do `(,_ ,E . ,D) ← get
              (put `(,S ,E . ,D))))
        (define (put-E E)
          (do `(,S ,_ . ,D) ← get
              (put `(,S ,E . ,D))))
        (define (put-D D)
          (do `(,S ,E . ,_) ← get
              (put `(,S ,E . ,D))))

        (define/match (apply-δ oⁿ S)
          [((or 'add1 'sub1 'iszero) `(,(? b? b) ,V ...))
           `(,(δ oⁿ `(,b)) ,@V)]
          [((or '+ '- '* '↑) `(,(? b? b₂) ,(? b? b₁) ,V ...))
           `(,(δ oⁿ `(,b₁ ,b₂)) ,@V)]
          [(_ _) (error 'apply-δ "failed: ~s ~s" oⁿ S)])]

  [`(,(? b? b) ,C ...)
   S ← get-S
   (put-S (cons b S))
   `(,@C)
   "secd1"]

  [`(,X ,C ...)
   S ← get-S
   E ← get-E
   V ≔ (E X)
   (put-S (cons V S))
   `(,@C)
   "secd2"]

  [`((,(? oⁿ? oⁿ) ,M ...) ,C ...)
   `(,@M (prim ,oⁿ) ,@C)
   "secdPA"]

  [`((prim ,(? oⁿ? oⁿ)) ,C ...)
   S ← get-S
   (put-S (apply-δ oⁿ S))
   `(,@C)
   "secd3"]

  [`((,M₁ ,M₂) ,C ...)
   `(,M₁ ,M₂ (ap) ,@C)
   "secdLA"]

  [`((λ ,X ,M) ,C ...)
   S ← get-S
   E ← get-E
   (put-S (cons `((λ ,X ,M) ,E) S))
   `(,@C)
   "secd4"]

  [`((ap) ,C ...)
   `(,V ((λ ,X ,M) ,E′) ,V′ ...) ← get-S
   E ← get-E
   D ← get-D
   (put-S '())
   (put-E (E′ X V))
   (put-D `((,@V′) ,E (,@C) ,D))
   `(,M)
   "secd5"]

  ['()
   `(,V ,_ ...) ← get-S
   `(,S′ ,E′ (,C′ ...) ,D) ← get-D
   (put-S (cons V S′))
   (put-E E′)
   (put-D D)
   `(,@C′)
   "secd6"])

(define-match-expander mkSECD
  ;; '(((Cs S) E) D)
  (syntax-parser
    [(_ S E Cs D)
     #'(cons (cons (cons Cs S) E) D)])
  (syntax-parser
    [(_ S E Cs D)
     #'(cons (cons (cons Cs S) E) D)]))

(define ⊢->secd (call-with-values
                (λ () (invoke-unit (⊢->secd-rules)))
                (λ (mrun reducer)
                  (λ (ς)
                    (match ς
                      [(mkSECD S E Cs D)
                       (mrun D E S (reducer Cs))])))))
(define ⊢->>secd (compose1 car (repeated ⊢->secd)))

(define/match (evalsecd m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>secd (mkSECD '() (↦) `(,M) 'ϵ))
     [(set (mkSECD `(,(? b? b)) E '() 'ϵ))
      b]
     [(set (mkSECD `(((λ ,X ,M) ,E′)) E '() 'ϵ))
      'function]
     [x (error 'evalsecd "invalid final state: ~a" x)])]
  [_ (error 'evalsecd "invalid input: ~a" m)])

(module+ test
  (check-equal? (⊢->>secd (mkSECD '() (↦ ['x 1])
                                  '((- (↑ 10 2) (* (add1 4) (+ x 2)))) 'ϵ))
                (set (mkSECD '(85) (↦ ['x 1]) '() 'ϵ)))
  (check-equal? (⊢->>secd (mkSECD '() (↦ ['x 1])
                                  '(((λ x (+ x x)) (add1 x))) 'ϵ))
                (set (mkSECD '(4) (↦ ['x 1]) '() 'ϵ)))
  (check-equal? (evalsecd '(- (↑ 10 2) (* (add1 4) (+ 1 2)))) 85)
  (check-equal? (evalsecd '((λ x (+ x x)) (add1 1))) 4)

  (check-equal? (evalsecd '(+ (* 9 (↑ 2 3)) 3)) 75)
  (check-equal? (evalsecd '(((λ f (λ x (f x))) (λ y (+ y y))) 8)) 16))

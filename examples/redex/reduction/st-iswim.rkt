#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/monad
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" [FV orig-FV] [subst orig-subst]
                  [v orig-v] [δ orig-δ]))
(provide ST-ISWIM FV subst ℬ Δ ⊢ v δ)

(module+ test (require rackunit))

;;=============================================================================
;; 10.1 Simply Typed ISWIM

(module BASE-ST-ISWIM racket/base
  (require lightstep/base lightstep/syntax)  
  (provide BASE-ST-ISWIM)

  (define (b? . _)  (error "to be implemented"))
  (define (B? . _)  (error "to be implemented"))
  (define (oⁿ? . _) (error "to beimplemented"))
  (define-language BASE-ST-ISWIM
    [M ∷=
       X
       `(λ [,X : ,T] ,M)
       `(,M₁ ,M₂)
       (? b?)
       `(,(? oⁿ?) ,M ...)]
    [T ∷=
       B
       `(,T₁ → ,T₂)]
    [X ∷= (? symbol? (? (compose1 not KWD?)))]
    [V ∷= (? b?) X `(λ [,X : ,T] ,M)]
    [KWD ∷= 'λ ': '→]

    [Γ ∷= (? map? X→T)]))

(require (submod "." BASE-ST-ISWIM))

(define-language ST-ISWIM #:super BASE-ST-ISWIM
  [B ∷= 'num]
  [b ∷= (? number?)]
  [oⁿ ∷= (? o¹?) (? o²?)]
  [o¹ ∷= 'add1 'sub1 'iszero]
  [o² ∷= '+ '- '* '↑]
  [KWD ∷= .... (? o¹?) (? o²?)])

;; M → 𝒫(X)
(define/match (FV m) #:super orig-FV
  [`(λ [,X : ,T] ,M) (set-remove (FV M) X)])

;; M X M → M
(define/match (subst m₁ x₂ m₂) #:super orig-subst
  [(`(λ [,X₁ : ,T] ,M₁) X₂ M₂)
   #:when (eq? X₁ X₂)
   `(λ [,X₁ : ,T] ,M₁)]
  [(`(λ [,X₁ : ,T] ,M₁) X₂ M₂)
   (let ([X₃ ((symbol-not-in (FV `(λ [,X₁ : ,T] ,M₁)) (FV M₂)) X₁)])
     `(λ [,X₃ : ,T] ,(subst (subst M₁ X₁ X₃) X₂ M₂)))])

;; b → T
(define/match (ℬ b)
  [(? b?) 'num])

;; oⁿ List(T) → T
(define/match (Δ oⁿ Ts)
  [('add1   '(num)) 'num]
  [('sub1   '(num)) 'num]
  [('iszero '(num)) '(num → (num → num))]
  [('+ '(num num)) 'num]
  [('- '(num num)) 'num]
  [('* '(num num)) 'num]
  [('↑ '(num num)) 'num])

;; Γ ⊢ M : T
(define-reduction (⊢)
  [`(,Γ ,(? b? b))
   (ℬ b)]

  [`(,Γ ,X)
   (Γ X)]

  [`(,Γ (λ [,X : ,T] ,M))
   T′ ← (⊢ `(,(Γ X T) ,M))
   `(,T → ,T′)]

  [`(,Γ (,M₁ ,M₂))
   `(,T → ,T′) ← (⊢ `(,Γ ,M₁))
   (? (λ (t) (equal? t T))) ← (⊢ `(,Γ ,M₂))
   T′]

  [`(,Γ (,(? oⁿ? oⁿ) ,M ...))
   `(,B ...) ← (mapM (λ (m) (⊢ `(,Γ ,m))) M)
   (Δ oⁿ B)])

;; (Γ M) → 𝒫(T)
(define step-⊢ (call-with-values (λ () (⊢)) compose1))

;; M → T
(define (type-of M)
  (match (step-⊢ `(,(↦) ,M))
    [(set T) T]
    [_ (error "type error")]))

(module+ test
  (check-equal? (type-of '(+ 1 2)) 'num)
  (check-exn #rx"type error" (λ () (type-of '(+ 1 (λ [x : num] 9)))))
  (check-exn #rx"type error" (λ () (type-of '(5 (λ [x : num] x)))))
  (check-exn #rx"type error" (λ () (type-of '(((λ [x : num] x) 5)
                                              (λ [x : num] x)))))
  (check-equal? (type-of '(+ 1 ((λ [y : num] 13) 42))) 'num)
  (check-equal? (type-of '(λ [x : num] (+ x 3))) '(num → num))
  (check-equal? (type-of '((λ [f : (num → num)] (f 0))
                           (λ [y : num] (add1 y))))
                'num)
  (check-equal? (type-of '(((λ [x : num]
                              (λ [y : (num → (num → (num → num)))] (y x)))
                            10)
                           (λ [z : num] (iszero z))))
                '(num → (num → num))))

;; re-interpret M
(define-match-expander ECxt
  (syntax-parser
    [(ECxt p)
     #'(cxt ECxt [□ (and p (or `(,(? V?) ,(? V?))
                               `(,(? oⁿ?) ,(? V?) (... ...))))]
            `(,V ,□)
            `(,□ ,M)
            `(,(? oⁿ?) ,V (... ...) ,□ ,M (... ...)))]))

;; oⁿ List(b) → V
(define/match (δ o bs) #:super orig-δ
  [('iszero `(0))
   '(λ [x : num] (λ [y : num] x))]
  [('iszero `(,(? number? n)))
   #:when (not (zero? n))
   '(λ [x : num] (λ [y : num] y))])

;; M --> M
(define-reduction (v) #:super [(orig-v)]
  [`((λ [,X : ,T] ,M) ,V)
   (subst M X V)])

;; M --> M
(define-reduction (⊢->v)
  #:do [(define →v (reducer-of (v)))]
  [(ECxt M)
   M′ ← (→v M)
   (ECxt M′)])

;; M → 𝒫(M)
(define step⊢->v (call-with-values (λ () (⊢->v)) compose1))
(define ⊢->>v (compose1 car (repeated step⊢->v)))

;; M → V
(define/match (evalᵥˢ m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>v M)
    [(set (? b? b)) b]
    [(set `(λ [,X : ,T] ,M)) 'function]
    [x (error 'evalᵥˢ "invalid answer: ~s" x)])]
  [_ (error 'evalᵥˢ "invalid input: ~s" m)])

(module+ test
  (check-equal? (evalᵥˢ '(+ ((λ [x : num] ((λ [y : num] y) x)) (- 2 1)) 8)) 9))

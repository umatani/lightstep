#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax
         (only-in "st-iswim.rkt"
                  ST-ISWIM [FV orig-FV] [subst orig-subst]
                  ℬ Δ [⊢ orig-⊢] [v orig-v] δ))

(module+ test (require rackunit))

;;=============================================================================
;; 10.3 Recursive Simply Typed ISWIM

(define-language REC-ST-ISWIM #:super ST-ISWIM
  [M ∷= .... `(fix ,M)]
  [KWD ∷= .... 'fix])

;; M → 𝒫(X)
(define/match (FV m) #:super orig-FV
  [`(fix ,M) (FV M)])

;; M X M → M
(define/match (subst m₁ x₂ m₂) #:super orig-subst
  [(`(fix ,M) X₂ M₂) `(fix ,(subst M X₂ M₂))])

;; Γ ⊢ M : T
(define-reduction (⊢) #:super [(orig-⊢)]
  [`(,Γ (fix ,M))
   `(,T → ,T′) ← (⊢ `(,Γ ,M))
   #:when (equal? T T′)
   T])

;; (Γ M) → 𝒫(T)
(define step-⊢ (call-with-values (λ () (⊢)) compose1))

;; M → T
(define (type-of M)
  (match (step-⊢ `(,(↦) ,M))
    [(set T) T]
    [_ (error "type error")]))

(module+ test
  (check-equal? (type-of '(fix (λ [x : num] x))) 'num))

;; M --> M
(define-reduction (y)
  [`(fix (λ [,X : ,T] ,M))
   (subst M X `(fix (λ [,X : ,T] ,M)))])

;; M --> M
(define-reduction (v) #:super [(y) (orig-v)])

;; re-interpret M
(define-match-expander ECxt
  (syntax-parser
    [(ECxt p)
     #'(cxt ECxt [□ (and p (or `(,(? V?) ,(? V?))
                               `(,(? oⁿ?) ,(? V?) (... ...))
                               `(fix (λ [,(? X?) : ,(? T?)] ,(? M?))) ;; NEW
                               ))]
            `(,V ,□)
            `(,□ ,M)
            `(,(? oⁿ?) ,V (... ...) ,□ ,M (... ...))
            `(fix ,□) ;; NEW
            )]))

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
  (check-equal? (evalᵥˢ '(+ ((λ [x : num] ((λ [y : num] y) x)) (- 2 1)) 8)) 9)

  ;; M M M → M
  (define (IF0 L M N)
    (let ([X ((symbol-not-in (FV M) (FV N)) 'if0)])
      `((((iszero ,L) (λ [,X : num] ,M)) (λ [,X : num] ,N)) 0)))

  ;; M
  (define mksum `(λ [s : (num → num)]
                   (λ [n : num]
                     ,(IF0 'n 'n '(+ n (s (- n 1)))))))

  (check-equal? (evalᵥˢ `((fix ,mksum) 10)) 55))

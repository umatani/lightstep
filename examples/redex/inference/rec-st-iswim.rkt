#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/monad
         lightstep/inference
         (only-in racket/match define-match-expander)
         (only-in "st-iswim.rkt"
                  ST-ISWIM [FV orig-FV] [subst orig-subst]
                  ℬ Δ [⊢-rules orig-⊢-rules] [v-rules orig-v-rules] δ))

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
(define-inference (⊢-rules) #:super [(orig-⊢-rules)]
  ;; TODO: inherit?
  #:forms ([`(,Γ:i ⊢ ,M:i : ,T:o) #:where T ← (⊢ `(,Γ ,M))])

  [`(,Γ ⊢ ,M : (,T → ,T′))
   #:when (equal? T T′)
   -----------------------
   `(,Γ ⊢ (fix ,M) : ,T)  ])

;; (Γ M) → 𝒫(T)
(define ⊢ (call-with-values (λ () (⊢-rules)) compose1))

;; M → T
(define (type-of M)
  (match (⊢ `(,(↦) ,M))
    [(set T) T]
    [_ (error "type error")]))

(module+ test
  (check-equal? (type-of '(fix (λ [x : num] x))) 'num))

;; M --> M
(define-inference (y-rules)
  [----------------------------------------------------------------
   `((fix (λ [,X : ,T] ,M)) → ,(subst M X `(fix (λ [,X : ,T] ,M))))])

;; M --> M
(define-inference (v-rules) #:super [(y-rules) (orig-v-rules)])

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
(define-inference (⊢->v-rules)
  #:do [(define rv (reducer-of (v-rules)))]
  #:forms (.... [`(,i →v ,o) #:where o ← (rv i)])
  [`(,M →v ,M′)
   -------------------------
   `(,(ECxt M) → ,(ECxt M′))])

;; M → 𝒫(M)
(define ⊢->v (call-with-values (λ () (⊢->v-rules)) compose1))
(define ⊢->>v (compose1 car (repeated ⊢->v)))

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

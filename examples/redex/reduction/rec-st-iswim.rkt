#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/monad
         (only-in racket/match define-match-expander)
         (only-in "st-iswim.rkt"
                  ST-ISWIM [FV orig-FV] [subst orig-subst]
                  ℬ Δ [⊢ orig-⊢] [v orig-v] δ))

(module+ test (require rackunit))

;;=============================================================================
;; 10.3 Recursive Simply Typed ISWIM

(define-language REC-ST-ISWIM #:super ST-ISWIM
  [M ∷= .... `(fix ,M)]
  [KWD ∷= .... 'fix])

(define/match (FV m) #:super orig-FV
  [`(fix ,M) (FV M)])

(define/match (subst m₁ x₂ m₂) #:super orig-subst
  [(`(fix ,M) X₂ M₂) `(fix ,(subst M X₂ M₂))])

(define-reduction (⊢) #:super [(orig-⊢)]
  [`(,Γ (fix ,M))
   `(,T → ,T′) ← (⊢ `(,Γ ,M))
   #:when (equal? T T′)
   T])

(define step-⊢ (call-with-values (λ () (⊢)) compose1))

(define (type-of M)
  (match (step-⊢ `(,(↦) ,M))
    [(set T) T]
    [_ (error "type error")]))

(module+ test
  (check-equal? (type-of '(fix (λ [x : num] x))) 'num))

(define-reduction (y)
  [`(fix (λ [,X : ,T] ,M))
   (subst M X `(fix (λ [,X : ,T] ,M)))])

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

(define-reduction (⊢->v)
  #:do [(define →v (reducer-of (v)))]
  [(ECxt M)
   M′ ← (→v M)
   (ECxt M′)])

(define step⊢->v (call-with-values (λ () (⊢->v)) compose1))
(define ⊢->>v (compose1 car (repeated step⊢->v)))

(define/match (evalᵥˢ m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>v M)
    [(set (? b? b)) b]
    [(set `(λ [,X : ,T] ,M)) 'function]
    [x (error 'evalᵥˢ "invalid answer: ~a" x)])]
  [_ (error 'evalᵥˢ "invalid input: ~a" m)])

(module+ test
  (check-equal? (evalᵥˢ '(+ ((λ [x : num] ((λ [y : num] y) x)) (- 2 1)) 8)) 9)

  (define (IF0 L M N)
    (let ([X ((symbol-not-in (FV M) (FV N)) 'if0)])
      `((((iszero ,L) (λ [,X : num] ,M)) (λ [,X : num] ,N)) 0)))

  (define mksum `(λ [s : (num → num)]
                   (λ [n : num]
                     ,(IF0 'n 'n '(+ n (s (- n 1)))))))

  (check-equal? (evalᵥˢ `((fix ,mksum) 10)) 55))

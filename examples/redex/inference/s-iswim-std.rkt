#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/inference
         (only-in "s-iswim.rkt" [S-ISWIM orig-S-ISWIM] FV s-rules s))

(module+ test (require rackunit))

;;=============================================================================
;; 9.3 Standard Reduction for State ISWIM

;; (define/match (E? m)
;;   [(E _) #t]
;;   [_ #f])

(define-language S-ISWIM #:super orig-S-ISWIM
  ;[Eₛ ∷= (? E?) `(letrec ,Σ ,(? E?))]
  )

(define-match-expander E
  (syntax-parser
    [(E p)
     #'(... (cxt E [□ (and p (? (λ (m) (not (∅? (s m))))))]
                 `(,V ,□)
                 `(,□ ,M)
                 `(,(? oⁿ?) ,V ... ,□ ,M ...)
                 `(set ,X ,□) ; NEW
                 ))]))

;; M --> M
(define-inference (⊢->s-rules)
  #:do [(define rs (reducer-of (s-rules)))]
  #:forms (.... [`(,i →s ,o) #:where o ← (rs i)])

  [`(,M →s ,M′)
   -------------------
   `(,(E M) → ,(E M′))]

  [`(,M →s ,M′)
   -------------------------------------------
   `((letrec ,Σ ,(E M)) → (letrec ,Σ ,(E M′)))])

;; M → 𝒫(M)
(define ⊢->s (call-with-values (λ () (⊢->s-rules)) compose1))
(define ⊢->>s (compose1 car (repeated ⊢->s)))

;; M → V
(define/match (evalₛˢ m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>s M)
    [(set (or (? b? b) `(letrec ,(? Σ?) ,(? b? b)))) b]
    [(set (or `(λ ,X ,M) `(letrec ,(? Σ?) (λ ,X ,M)))) 'function]
    [x (error 'evalₛˢ "invalid answer: ~s" x)])]
  [_ (error 'evalₛˢ "invalid input: ~s" m)])

(module+ test
  (check-equal? (evalₛˢ `((λ x (+ 3 (letrec ,(↦ ['y 1])
                                     ((λ z (+ z y))
                                      (set x (+ x 1))))))
                         0))
                4))

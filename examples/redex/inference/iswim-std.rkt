#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/inference
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" [ISWIM orig-ISWIM] FV subst δ v-rules))

(module+ test (require rackunit))

;;=============================================================================
;; 5 An Abstract Syntax Machine
;;=============================================================================

;;=============================================================================
;; 5.1 Standard Reductions

(define-language ISWIM #:super orig-ISWIM)

(define-match-expander E
  (syntax-parser
    [(E p)
     #'(cxt E [□ (and p (or `(,(? V?) ,(? V?))
                            `(,(? oⁿ?) ,(? V?) (... ...))))]
            `(,V ,□)
            `(,□ ,M)
            `(,(? oⁿ?) ,V (... ...) ,□ ,M (... ...)))]))

;; M --> M
(define-inference (⊢->v-rules)
  #:do [(define rv (reducer-of (v-rules)))]
  #:forms (.... [`(,i →v ,o) #:where o ← (rv i)])
  [`(,M →v ,M′)
   -------------------------
   `(,(E M) → ,(E M′))])

;; M → 𝒫(M)
(define ⊢->v (call-with-values (λ () (⊢->v-rules)) compose1))
(define ⊢->>v (compose1 car (repeated ⊢->v)))

;; M → V
(define/match (evalᵥˢ m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>v M)
    [(set (? b? b)) b]
    [(set `(λ ,X ,M)) 'function]
    [x (error 'evalᵥˢ "invalid answer: ~s" x)])]
  [_ (error 'evalᵥˢ "invalid input: ~s" m)])

(module+ test
  (check-equal? (evalᵥˢ '(+ ((λ x ((λ y y) x)) (- 2 1)) 8)) 9))

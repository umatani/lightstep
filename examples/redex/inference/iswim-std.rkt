#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/inference
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" [ISWIM orig-ISWIM] FV subst δ v))

(module+ test (require rackunit))

;;=============================================================================
;; 5 An Abstract Syntax Machine
;;=============================================================================

;;=============================================================================
;; 5.1 Standard Reductions

(define-language ISWIM #:super orig-ISWIM)

(define-match-expander E
  (syntax-parser
    [(E □)
     #'(cxt E [□ (and □ (or `(,(? V?) ,(? V?))
                            `(,(? oⁿ?) ,(? V?) (... ...))))]
            `(,V ,□)
            `(,□ ,M)
            `(,(? oⁿ?) ,V (... ...) ,□ ,M (... ...)))]))

(define-inference (⊢->v)
  #:do [(define rv (reducer-of (v)))]
  #:forms (.... [`(,i →v ,o) #:where o ← (rv i)])
  [`(,m →v ,M′)
   -------------------------
   `(,(E m) → ,(E M′))])

(define step⊢->v (call-with-values (λ () (⊢->v)) compose1))
(define ⊢->>v (compose1 car (repeated step⊢->v)))

(define/match (evalᵥˢ m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>v M)
    [(set (? b? b)) b]
    [(set `(λ ,X ,M)) 'function]
    [x (error 'evalᵥˢ "invalid answer: ~a" x)])]
  [_ (error 'evalᵥˢ "invalid input: ~a" m)])

(module+ test
  (check-equal? (evalᵥˢ '(+ ((λ x ((λ y y) x)) (- 2 1)) 8)) 9))

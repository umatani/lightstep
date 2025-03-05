#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax
         (only-in racket/unit invoke-unit)
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" [ISWIM orig-ISWIM] FV subst δ v))
(provide ECxt)

(module+ test (require rackunit))

;;=============================================================================
;; 5 An Abstract Syntax Machine
;;=============================================================================

;;=============================================================================
;; 5.1 Standard Reductions

(define-language ISWIM #:super orig-ISWIM)

(define-match-expander ECxt
  (syntax-parser
    [(ECxt □)
     #'(cxt ECxt [□ (and □ (or `(,(? V?) ,(? V?))
                               `(,(? oⁿ?) ,(? V?) (... ...))))]
            `(,V ,□)
            `(,□ ,M)
            `(,(? oⁿ?) ,V (... ...) ,□ ,M (... ...)))]))

(define-reduction (⊢->v-rules)
  [(ECxt m)
   M′ ← (v m)
   (ECxt M′)])

(define ⊢->v (call-with-values
             (λ () (invoke-unit (⊢->v-rules)))
             compose1))
(define ⊢->>v (compose1 car (repeated ⊢->v)))

(define/match (evalᵥˢ m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>v M)
    [(set (? b? b)) b]
    [(set `(λ ,X ,M)) 'function]
    [x (error 'evalᵥˢ "invalid answer: ~a" x)])]
  [_ (error 'evalᵥˢ "invalid input: ~a" m)])

(module+ test
  (check-equal? (evalᵥˢ '(+ ((λ x ((λ y y) x)) (- 2 1)) 8)) 9)
  )

#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax
         (only-in "iswim.rkt" βv-rule)
         (only-in "e-iswim.rkt" δ δ-rule)
         (only-in "h-iswim.rkt" return-rule δerr-rule)
         (only-in "c-iswim.rkt" [C-ISWIM orig-C-ISWIM] FV subst FCxt))

(module+ test (require rackunit))

;;=============================================================================
;; 8.4 Standard Reduction for Control ISWIM

(define-language C-ISWIM #:super orig-C-ISWIM)

(define-match-expander ECxt
  (syntax-parser
    [(ECxt p)
     #'(... (cxt ECxt [□ p]
                 `(,V ,□)
                 `(,□ ,M)
                 `(,(? oⁿ?) ,V ... ,□ ,M ...)
                 `(catch ,□ with (λ ,X₁ (λ ,X₂ ,M))) ;; NEW
                 ))]))

;; M --> M
(define-reduction (c̃) #:super [(βv-rule) (δ-rule δ) (δerr-rule δ)
                                         (return-rule)])

;; M --> M
(define-reduction (⊢->c)
  #:do [(define →c̃ (reducer-of (c̃)))]

  [(ECxt `(,V₁ ,V₂))
   M ← (→c̃ `(,V₁ ,V₂))
   (ECxt M)]

  [(ECxt `(,(? oⁿ? oⁿ) ,V ...))
   M ← (→c̃ `(,oⁿ ,@V))
   (ECxt M)]

  [(ECxt `(catch ,V with (λ ,X₁ (λ ,X₂ ,M))))
   M′ ← (→c̃ `(catch ,V with (λ ,X₁ (λ ,X₂ ,M))))
   (ECxt M′)]

  [(ECxt `(catch ,(FCxt `(throw ,(? b? b))) with (λ ,X₁ (λ ,X₂ ,M))))
   (ECxt `(((λ ,X₁ (λ ,X₂ ,M)) ,b) (λ Z ,(FCxt 'Z))))]

  [(and x (FCxt `(throw ,(? b? b))))
   #:when (not (equal? x `(throw ,b)))
   `(throw ,b)])

;; M → 𝒫(M)
(define step⊢->c (call-with-values (λ () (⊢->c)) compose1))
(define ⊢->>c (compose1 car (repeated step⊢->c)))

;; M → (V ∪ ⊥)
(define/match (evalcˢ m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>c M)
    [(set (? b? b)) b]
    [(set `(λ ,X ,M)) 'function]
    [(set `(throw ,b)) `(err ,b)]
    [x (error 'evalcˢ "invalid answer: ~s" x)])]
  [_ (error 'evalcˢ "invalid input: ~s" m)])

(module+ test
  (check-exn #rx"invalid input" (λ () (evalcˢ '(+ 1 x))))
  (check-equal? (evalcˢ '(+ ((λ x x) 8) 2)) 10)
  (check-equal? (evalcˢ '((λ x x) (λ x x))) 'function)
  
  (check-equal? (evalcˢ '(add1 (λ x x))) '(err 0))
  (check-equal? (evalcˢ '(/ 3 0)) '(err 0))

  (check-equal? (step⊢->c '(+ (- 4 (throw 1)) (throw 2)))
                (set '(throw 1)))
  (check-equal? (⊢->>c '(+ (- 4 (throw 1)) (throw 2)))
                (set '(throw 1)))

  (check-equal? (evalcˢ '(catch (add1 (/ 3 0))
                           with (λ x (λ f (f 10000))))) 10001))

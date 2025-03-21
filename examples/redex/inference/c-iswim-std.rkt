#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/inference
         (only-in "iswim.rkt" βv-rules)
         (only-in "e-iswim.rkt" δ δ-rules)
         (only-in "h-iswim.rkt" return-rules δerr-rules)
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
(define-inference (c̃-rules) #:super [(βv-rules) (δ-rules δ) (δerr-rules δ)
                                                (return-rules)])

;; M --> M
(define-inference (⊢->c-rules)
  #:do [(define rc̃ (reducer-of (c̃-rules)))]
  #:forms ([`(,i:i →c ,o:o) #:where o ← (⊢->c-rules i)]
           [`(,i   →c̃ ,o  ) #:where o ← (rc̃         i)])

  [`((,V₁ ,V₂) →c̃ ,M)
   ----------------------------------
   `(,(ECxt `(,V₁ ,V₂)) →c ,(ECxt M))]

  [`((,oⁿ ,@V) →c̃ ,M)
   ---------------------------------------------
   `(,(ECxt `(,(? oⁿ? oⁿ) ,V ...)) →c ,(ECxt M))]

  [`((catch ,V with (λ ,X₁ (λ ,X₂ ,M))) →c̃ ,M′)
   ------------------------------------------------------------
   `(,(ECxt `(catch ,V with (λ ,X₁ (λ ,X₂ ,M)))) →c ,(ECxt M′))]

  [---------------------------------------------------------------------
   `(,(ECxt `(catch ,(FCxt `(throw ,(? b? b))) with (λ ,X₁ (λ ,X₂ ,M))))
     →c ,(ECxt `(((λ ,X₁ (λ ,X₂ ,M)) ,b) (λ Z ,(FCxt 'Z)))))            ]

  [#:when (not (equal? x `(throw ,b)))
   ---------------------------------------------------
   `(,(and x (FCxt `(throw ,(? b? b)))) →c (throw ,b))])

;; M → 𝒫(M)
(define ⊢->c (call-with-values (λ () (⊢->c-rules)) compose1))
(define ⊢->>c (compose1 car (repeated ⊢->c)))

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

  (check-equal? (⊢->c '(+ (- 4 (throw 1)) (throw 2)))
                (set '(throw 1)))
  (check-equal? (⊢->>c '(+ (- 4 (throw 1)) (throw 2)))
                (set '(throw 1)))

  (check-equal? (evalcˢ '(catch (add1 (/ 3 0))
                           with (λ x (λ f (f 10000))))) 10001))

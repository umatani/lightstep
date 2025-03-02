#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax
         (only-in racket/unit invoke-unit)
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" [ISWIM orig-ISWIM] subst δ))

(module+ test (require rackunit))

(define-language ISWIM #:super orig-ISWIM)

;;=============================================================================
;; 6.1 The CC Machine

(define-match-expander ECxt
  (syntax-parser
    [(ECxt □:id)
     #'(ECxt □ #:hole □)]
    [(ECxt p #:hole □:id)
     #'(... (cxt ECxt [□ p]
                 `(,V ,□)
                 `(,□ ,M)
                 `(,(? oⁿ?) ,V ... ,□ ,M ...)))]))

(define-reduction (⊢->cc-rules)
  [`((,M₁ ,M₂) ,(ECxt □))
   #:when (not (V? M₁))
   `(,M₁ ,(ECxt `(,□ ,M₂)))
   "cc1"]

  [`((,V ,M) ,(ECxt □))
   #:when (not (V? M))
   `(,M ,(ECxt `(,V ,□)))
   "cc2"]

  [`((,(? oⁿ? oⁿ) ,V ... ,M₁ ,M ...) ,(ECxt □))
   #:when (not (V? M₁))
   `(,M₁ ,(ECxt `(,oⁿ ,@V ,□ ,@M)))
   "cc3"]

  [`(((λ ,X ,M) ,V) ,ECxt)
   `(,(subst M X V) ,ECxt)
   "ccfiᵥ"]

  [`((,(? oⁿ? oⁿ) ,(? b? b) ...) ,ECxt)
   `(,(δ oⁿ b) ,ECxt)
   "ccffi"]

  [`(,V ,(ECxt `(,V′ ,□) #:hole □))
   `((,V′ ,V) ,(ECxt □))
   "cc4"]

  [`(,V ,(ECxt `(,□ ,M) #:hole □))
   `((,V ,M) ,(ECxt □))
   "cc5"]

  [`(,V ,(ECxt `(,(? oⁿ? oⁿ) ,V′ ... ,□ ,M ...) #:hole □))
   `((,oⁿ ,@V′ ,V ,@M) ,(ECxt □))
   "cc6"])


(define ⊢->cc (call-with-values
               (λ () (invoke-unit (⊢->cc-rules)))
               compose1))
(define ⊢->>cc (compose1 car (repeated ⊢->cc)))

(define □-cc #())

(module+ test
  (⊢->>cc `((((λ x x) (λ y y)) g) ,□-cc))
  (⊢->>cc `((((λ x x) n) p) ,□-cc))
  (⊢->>cc `((+ (* 9 (↑ 2 3)) 3) ,□-cc)))

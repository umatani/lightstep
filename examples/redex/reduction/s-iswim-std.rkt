#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax
         (only-in racket/match define-match-expander)
         (only-in "s-iswim.rkt" [S-ISWIM orig-S-ISWIM] FV s step-s))

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
    [(E □)
     #'(... (cxt E [□ (and □ (? (λ (m) (not (∅? (step-s m))))))]
                 `(,V ,□)
                 `(,□ ,M)
                 `(,(? oⁿ?) ,V ... ,□ ,M ...)
                 `(set ,X ,□) ; NEW
                 ))]))

(define-reduction (⊢->s)
  #:do [(define →s (reducer-of (s)))]
  [(E m)
   M′ ← (→s m)
   (E M′)]
  [`(letrec ,Σ ,(E m))
   M′ ← (→s m)
   `(letrec ,Σ ,(E M′))])

(define step⊢->s (call-with-values (λ () (⊢->s)) compose1))
(define ⊢->>s (compose1 car (repeated step⊢->s)))

(define/match (evalₛˢ m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>s M)
    [(set (or (? b? b) `(letrec ,(? Σ?) ,(? b? b)))) b]
    [(set (or `(λ ,X ,M) `(letrec ,(? Σ?) (λ ,X ,M)))) 'function]
    [x (error 'evalₛˢ "invalid answer: ~a" x)])]
  [_ (error 'evalₛˢ "invalid input: ~a" m)])

(module+ test
  (check-equal? (evalₛˢ `((λ x (+ 3 (letrec ,(↦ ['y 1])
                                     ((λ z (+ z y))
                                      (set x (+ x 1))))))
                         0))
                4))

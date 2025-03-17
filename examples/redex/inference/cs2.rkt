#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/inference
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" δ)
         (only-in "s-iswim.rkt" [S-ISWIM orig-S-ISWIM] FV AV substs subst)
         (only-in "cs.rkt" [⊢->cs-rules orig-⊢->cs-rules] mkCS))

(module+ test (require rackunit))

;;=============================================================================
;; 9.3 The CS Machine extended with letrec construct

(define-language S-ISWIM #:super orig-S-ISWIM)

;; re-interpret M
(define-match-expander E
  (syntax-parser
    [(E p)
     #'(... (cxt E [□ p]
                 `(,V ,□)
                 `(,□ ,M)
                 `(,(? oⁿ?) ,V ... ,□ ,M ...)
                 `(set ,X ,□) ; NEW
                 ))]))

;; (M Σ) --> (M Σ)
(define-inference (⊢->cs-rules) #:super [(orig-⊢->cs-rules)]
  #:do [(define (substs-Σ Σ xs ms)
          (for/map ([(x v) (in-map Σ)])
            (values (substs x xs ms) (substs v xs ms))))]

  [Σ ← get
   `(,X′ ...) ≔ (set→list (dom Σ′))
   `(,(? X? Y) ...) ≔ (map (symbol-not-in (dom Σ)) X′)
   (put (⊔ Σ (substs-Σ Σ′ X′ Y)))
   --------------------------------------------------- "csR"
   `(,(E `(letrec ,Σ′ ,M)) → ,(E (substs M X′ Y)))          ])

;; (M Σ) → 𝒫((M Σ))
(define ⊢->cs (let-values ([(mrun reducer) (⊢->cs-rules)])
                (match-λ
                 [(mkCS M Σ)
                  (mrun Σ (reducer M))])))
(define ⊢->>cs (compose1 car (repeated ⊢->cs)))

;; M → V
(define/match (evalcs m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>cs (mkCS M (↦)))
     [(set (mkCS (? b? b) Σ))
      b]
     [(set (mkCS `(λ ,X ,M) Σ))
      'function]
     [x (error 'evalcs "invalid final state: ~s" x)])]
  [_ (error 'evalcs "invalid input: ~s" m)])

(module+ test
  (check-equal? (evalcs '((λ y (+ 1 ((λ x (* (add1 x) y)) (set y 3)))) 2))
                10)

  (check-equal? (evalcs `(+ 3 (letrec ,(↦ ['y 1])
                                ((λ z (+ z y)) 8))))
                12)

  (check-equal? (evalcs `((λ x (+ 3 (letrec ,(↦ ['y 1])
                                      ((λ z (+ z y))
                                       (set x (+ x 1))))))
                          0))
                4))

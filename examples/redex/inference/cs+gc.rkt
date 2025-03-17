#lang racket/base
(require lightstep/base lightstep/syntax lightstep/inference
         (only-in "iswim.rkt" δ)
         (only-in "cs.rkt" [S-ISWIM orig-S-ISWIM] AV FV subst E
                  ⊢->cs-rules mkCS))

(module+ test (require rackunit))

;;=============================================================================
;; 9.5 The CS Machine with GC

(define-language S-ISWIM #:super orig-S-ISWIM)

;; Σ 𝒫(X) → Σ
(define (gc Σ₀ Xs₀)
  (define (aux Σ Xs)
    (for/fold ([Σ Σ] [Xs Xs])
              ([(X V) (in-map Σ₀)])
      (if (∈ X Xs)
        (values (Σ X V) (∪ Xs (FV V)))
        (values Σ Xs))))
  (let loop ([Σ (↦)]
             [Xs Xs₀])
    (define-values (Σ′ Xs′) (aux Σ Xs))
    (if (equal? Σ Σ′)
      Σ
      (loop Σ′ Xs′))))

;; (M Σ) --> (M Σ)
(define-inference (⊢->cs+gc-rules) #:super [(⊢->cs-rules)]
  [Σ ← get
   Σ′ ≔ (gc Σ (FV M))
   #:when (not (equal? Σ Σ′))
   (put Σ′)
   -------------------------- "csgc"
   `(,M → ,M)                       ])

;; (M Σ) → 𝒫((M Σ))
(define ⊢->cs+gc (let-values ([(mrun reducer) (⊢->cs+gc-rules)])
                   (match-λ
                    [(mkCS M Σ) (mrun Σ (reducer M))])))
(define ⊢->>cs+gc (compose1 car (repeated ⊢->cs+gc)))

;; M → V
(define/match (evalcs+gc m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>cs+gc (mkCS M (↦)))
     [(set (mkCS (? b? b) Σ))
      b]
     [(set (mkCS `(λ ,X ,M) Σ))
      'function]
     [x (error 'evalcs+gc "invalid final state: ~s" x)])]
  [_ (error 'evalcs+gc "invalid input: ~s" m)])


(module+ test
  (require (only-in "cs.rkt" LET SEQ))

  (check-equal? (⊢->>cs+gc (mkCS `((λ x ,(SEQ '(set x (* x x)) '(add1 x))) 8)
                                 (↦)))
                (set (cons 65 (↦))))

  (check-equal? (⊢->>cs+gc (mkCS (LET '([x 0])
                                      (SEQ '(set x 5)
                                           (LET '([x 9]) (SEQ '(set x (+ x x))
                                                              'x)))) (↦)))
                (set (cons 18 (↦)))))

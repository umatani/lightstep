#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/inference
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" δ)
         (only-in "s-iswim.rkt" [S-ISWIM orig-S-ISWIM] FV AV substs subst E))

(module+ test (require rackunit))

;;=============================================================================
;; 9.3 Revised Standard Reduction for State ISWIM

(define-language S-ISWIM #:super orig-S-ISWIM)

(define-match-expander Eₛ
  (syntax-parser
    [(Eₛ p)
     #'(cxt1 Eₛ [□ p]
             `(letrec ,x ,□)
             □)]))

;; M --> M
(define-inference (⊢->s2-rules)
  #:do [(define (substs-Σ Σ xs ms)
          (for/map ([(x v) (in-map Σ)])
            (values (substs x xs ms) (substs v xs ms))))]

  [#:when (not (∈ X (AV M)))
   ------------------------------------------------------ "s2fiᵥ"
   `(,(Eₛ (E `((λ ,X ,M) ,V))) → ,(Eₛ (E (subst M X V))))        ]

  [------------------------------------------------------- "s2ffi"
   `(,(Eₛ (E `(,(? oⁿ? oⁿ) ,V ...))) → ,(Eₛ (E (δ oⁿ V))))        ]

  [#:when (∈ X (AV M))
   ---------------------------------------------------------------- "s2fiₛ"
   `(,(Eₛ (E `((λ ,X ,M) ,V))) → ,(Eₛ (E `(letrec ,(↦ [X V]) ,M))))        ]

  [#:when (not (equal? x `(letrec ,Σ ,M)))
   ---------------------------------------------------- "s2liftE"
   `(,(and x (E `(letrec ,Σ ,M))) → (letrec ,Σ ,(E M)))          ]

  [`(,X′ ...) ≔ (set→list (dom Σ′))
   `(,(? X? Y) ...) ≔ (map (symbol-not-in (dom Σ)) X′)
   Σ″ ≔ (⊔ Σ (substs-Σ Σ′ X′ Y))
   --------------------------------------------------- "s2liftR"
   `((letrec ,Σ ,(E `(letrec ,Σ′ ,M)))
     → (letrec ,Σ″ ,(E (substs M X′ Y))))                       ]

  [#:when (map-∈ X Σ)
   ---------------------------------------------- "s2derefR"
   `((letrec ,Σ ,(E X)) → (letrec ,Σ ,(E (Σ X))))           ]

  [#:when (map-∈ X Σ)
   --------------------------------------------------------------- "s2assignR"
   `((letrec ,Σ ,(E `(set ,X ,V))) → (letrec ,(Σ X V) ,(E (Σ X))))            ])

;; M → 𝒫(M)
(define ⊢->s2 (call-with-values (λ () (⊢->s2-rules)) compose1))
(define ⊢->>s2 (compose1 car (repeated ⊢->s2)))

;; M → V
(define/match (evalₛ₂ m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>s2 M)
     [(set (or (? b? b) `(letrec ,(? Σ?) ,(? b? b)))) b]
     [(set (or `(λ ,X ,M) `(letrec ,(? Σ?) (λ ,X ,M)))) 'function]
     [x (error 'evalₛ₂ "invalid answer: ~s" x)])]
  [_ (error 'evalₛ₂ "invalid input: ~s" m)])

(module+ test
  (check-equal? (evalₛ₂ '((λ y (+ 1 ((λ x (* (add1 x) y)) (set y 3)))) 2))
                10)

  (check-equal? (evalₛ₂ `(+ 3 (letrec ,(↦ ['y 1])
                                ((λ z (+ z y)) 8))))
                12)

  (check-equal? (evalₛ₂ `((λ x (+ 3 (letrec ,(↦ ['y 1])
                                      ((λ z (+ z y))
                                       (set x (+ x 1))))))
                          0))
                4))

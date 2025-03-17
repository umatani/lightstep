#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/transformers
         lightstep/inference
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" ISWIM FV δ))
(provide CEK ⊢->cek-rules mkCEK)

(module+ test (require rackunit))

;;=============================================================================
;; 6.4 The CEK Machine

(define-language CEK #:super ISWIM
  [κ ∷=
     'mt
     `(fn (,V ,E) ,(? κ? κ))
     `(ar (,M ,E) ,(? κ? κ))
     `(op ,(? list? VEsOⁿ) ,(? list? MEs) ,(? κ? κ))]
  [E ∷= (? map? X→VE)])

;; (M E κ) --> (M E κ)
(define-inference (⊢->cek-rules)
  #:monad (StateT #f (NondetT ID))

  [κ ← get
   (put `(ar (,M₂ ,E) ,κ))
   ---------------------------- "cek1"
   `(((,M₁ ,M₂) ,E) → (,M₁ ,E))       ]

  [κ ← get
   (put `(op (,oⁿ) ,(map (λ (m) `(,m ,E)) M′) ,κ))
   ----------------------------------------------- "cek2"
   `(((,(? oⁿ? oⁿ) ,M ,M′ ...) ,E) → (,M ,E))            ]

  [#:when (not (X? V))
   `(fn ((λ ,X₁ ,M) ,E′) ,κ) ← get
   (put κ)
   ----------------------------------- "cek3"
   `((,V ,E) → (,M ,(E′ X₁ `(,V ,E))))       ]

  [#:when (not (X? V))
   `(ar (,M ,E′) ,κ) ← get
   (put `(fn (,V ,E) ,κ))
   ----------------------- "cek4"
   `((,V ,E) → (,M ,E′))         ]

  [`(op ((,(? b? b) ,E′) ... ,oⁿ) () ,κ) ← get
   (put κ)
   --------------------------------------------------------- "cek5"
   `((,(? b? bₙ) ,E) → (,(δ oⁿ (reverse (cons bₙ b))) ,(↦)))       ]

  [#:when (not (X? V))
   `(op (,c ... ,oⁿ) ((,M ,Eₘ) ,cₗ ...) ,κ) ← get
   (put `(op ((,V ,E) ,@c ,oⁿ) (,@cₗ) ,κ))
   ------------------------------------------------ "cek6"
   `((,V ,E) → (,M ,Eₘ))                                  ]

  [(↦ [x `(,V ,E′)]) ≔ E
   ---------------------------- "cek7"
   `((,(? X? x) ,E) → (,V ,E′))       ])

(define-match-expander mkCEK
  (syntax-parser
    [(_ M E κ) #'(cons `(,M ,E) κ)])
  (syntax-parser
    [(_ M E κ) #'(cons `(,M ,E) κ)]))

;; (M E κ) → 𝒫((M E κ))
(define ⊢->cek (let-values ([(mrun reducer) (⊢->cek-rules)])
                 (match-λ
                  [(mkCEK M E (? κ? κ))
                   (mrun κ (reducer `(,M ,E)))])))
(define ⊢->>cek (compose1 car (repeated ⊢->cek)))

;; M → V
(define/match (evalcek m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>cek (mkCEK M (↦) 'mt))
     [(set (mkCEK (? b? b) E 'mt))
      b]
     [(set (mkCEK `(λ ,X ,M) E 'mt))
      'function]
     [x (error 'evalcek "invalid final state: ~s" x)])]
  [_ (error 'evalcek "invalid input: ~s" m)])

(module+ test
  (require (only-in (submod "cc.rkt" test) Ω))
  
  (check-equal? (evalcek '(+ (* 9 (↑ 2 3)) 3)) 75)
  (check-equal? (evalcek '(((λ f (λ x (f x))) (λ y (+ y y))) 8)) 16)

  (check-equal? (⊢->>cek (mkCEK Ω (↦) 'mt)) ∅))

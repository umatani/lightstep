#lang racket/base
(require (for-syntax racket/base (only-in syntax/parse syntax-parser))
         lightstep/base lightstep/syntax lightstep/inference
         (only-in racket/match define-match-expander)
         (only-in "pcf.rkt" δ)
         (only-in "pcf-bigstep.rkt" PCF⇓))
(provide PCFρ vρ-rules injρ)

(module+ test (require rackunit))

;; TODO: monadic version

;;-----------------------------------------------------------------------------
;; 3.6 Explicit substitutions

(define-language PCFρ #:super PCF⇓
  [C ∷=
     V
     `(,M ,(? ρ?))
     `(if0 ,C₁ ,C₂ ,C₃)
     `(,C₀ ,C ...)]

  [redex ∷=
         `((if0 ,M ...) ,(? ρ?))
         `((,M ...) ,(? ρ?))
         `(,O ,(? ρ?))
         `(,N ,(? ρ?))
         `(,X ,(? ρ?))
         `(((λ ([,X : ,T] ...) ,M) ,(? ρ?)) ,V ...)
         `(((μ [,X′ : ,T′] (λ ([,X : ,T] ...) ,M)) ,(? ρ?)) ,V ...)
         `(,O ,V ...)
         `(if0 ,N ,C₁ ,C₂)])

(define-match-expander E
  (syntax-parser
    [(E p)
     #'(... (cxt E [□ (and p (? redex?))]
                 `(,V ... ,(? C? □) ,C ...)
                 `(if0 ,(? C? □) ,C₂ ,C₃)))]))

;; C --> C
(define-inference (vρ-rules)
  #:do [(define (ext Γ xs vs)
          (foldr (λ (x v Γ) (Γ x v)) Γ xs vs))]
  
  [-------------------------------------------------------------- "ρ-if"
   `(((if0 ,M ...) ,(? ρ? ρ)) → (if0 ,@(map (λ (m) `(,m ,ρ)) M)))       ]

  [------------------------------------------------------ "ρ-app"
   `(((,M ...) ,(? ρ? ρ)) → (,@(map (λ (m) `(,m ,ρ)) M)))        ]

  [---------------------- "ρ-op"
   `((,O ,(? ρ? ρ)) → ,O)       ]

  [---------------------- "ρ-num"
   `((,N ,(? ρ? ρ)) → ,N)        ]

  [V ≔ (ρ X)
   ---------------------- "ρ-x"
   `((,X ,(? ρ? ρ)) → ,V)      ]

  [------------------------------------------------------------------ "β"
   `((((λ ([,X : ,T] ...) ,M) ,(? ρ? ρ)) ,V ...) → (,M ,(ext ρ X V)))    ]

  [----------------------------------------------------------- "rec-β"
   `((,(and f `((μ [,Xₐ : ,Tₐ]
                   (λ ([,X : ,T] ...) ,M)) ,(? ρ? ρ))) ,V ...)
     → (,M ,(ext ρ (cons Xₐ X) (cons f V))))                          ]

  [V₁ ≔ (δ `(,O ,@V))
   -------------------- "δ"
   `((,O ,V ...) → ,V₁)    ]

  [------------------------ "if-t"
   `((if0 0 ,C₁ ,C₂) → ,C₁)       ]

  [#:when (not (equal? N 0))
   ------------------------- "if-f"
   `((if0 ,N ,C₁ ,C₂) → ,C₂)       ])

;; C --> C
(define-inference (-->vρ-rules)
  #:do [(define rvρ (reducer-of (vρ-rules)))]
  #:forms (.... [`(,i →vρ ,o) #:where o ← (rvρ i)])

  [`(,C →vρ ,C′)
   ------------------- "EC"
   `(,(E C) → ,(E C′))     ])

;; C → 𝒫(C)
(define -->vρ (call-with-values (λ () (-->vρ-rules)) compose1))

;; M → C
(define (injρ M)
  `(,M ,(↦)))

(module+ test
  (require (only-in (submod "pcf.rkt" test) fact-5))

  (check-equal? (car ((repeated -->vρ) (injρ fact-5))) (set 120)))

#lang racket/base
(require lightstep/base lightstep/syntax lightstep/inference
         (only-in "pcf.rkt" δ)
         (only-in "pcf-rho.rkt" vρ-rules)
         (only-in "pcf-varsigma.rkt" -->vς-rules)
         (only-in "pcf-sigma.rkt" injσ)
         (only-in "pcf-sigma-star.rkt" [PCFσ* orig-PCFσ*] alloc*)
         (only-in "pcf-sigma-sigma.rkt" -->vσ/Σ-rules))

(module+ test (require rackunit))

;;-----------------------------------------------------------------------------
;; 4.1 Abstracting over Σ (PCFσ*)

(define-language PCFσ* #:super orig-PCFσ*)

;; σ --> σ
(define-inference (-->vσ*/Σ-rules alloc* ext-Σ lookup-Σ)
  #:super [(-->vσ/Σ-rules alloc* ext-Σ lookup-Σ)]
  #:do [;; remove rules manually
        (define-inference (-->vς″-rules) #:super [(-->vς′-rules)]
          [#:when #f
           --------------- "ev-if"
           `(,x → ,(void))         ]
          [#:when #f
           --------------- "ev-app"
           `(,x → ,(void))         ]
          [#:when #f
           --------------- "co-if"
           `(,x → ,(void))         ]
          [#:when #f
           --------------- "co-app"
           `(,x → ,(void))         ])
        (define rvς″ (reducer-of (-->vς″-rules)))]

  #:forms (.... [`(,i →vς″ ,o) #:where o ← (rvς″ i)])

  ;; override with →vς″
  [`(,ς →vς″ ,ς′)
   ----------------------------- "ap"
   `((,(? ς? ς) ,Σ) →  (,ς′ ,Σ))     ]

  ; Eval
  [`(,A) ≔ (alloc* σ)
   ------------------------------------------------ "ev-if"
   `(,(and σ `(((if0 ,S₀ ,C₁ ,C₂) ,K) ,Σ))
     → ((,S₀ ((if0 □ ,C₁ ,C₂) ,A)) ,(ext-Σ Σ `(,A) `(,K))))        ]

  [`(,A) ≔ (alloc* σ)
   ------------------------------------------- "ev-app"
   `(,(and σ `(((,V ... ,S ,C ...) ,K) ,Σ))
     → ((,S ((,@V □ ,@C) ,A)) ,(ext-Σ Σ `(,A) `(,K))))         ]

  ; Continue
  [K ≔ (lookup-Σ Σ A)
   -------------------------------- "co-if"
   `(((,V ((if0 □ ,C₁ ,C₂) ,A)) ,Σ)
     → (((if0 ,V ,C₁ ,C₂) ,K) ,Σ))         ]

  [K ≔ (lookup-Σ Σ A)
   ------------------------------------ "co-app"
   `(((,V ((,V₀ ... □ ,C₀ ...) ,A)) ,Σ)
     → (((,@V₀ ,V ,@C₀) ,K) ,Σ))                ])

;; δ --> δ
(define-inference (-->vσ*/alloc-rules alloc*)
  #:super [(-->vσ*/Σ-rules alloc* ext lookup)])

;; σ → 𝒫(σ)
(define -->vσ* (call-with-values (λ () (-->vσ*/alloc-rules alloc*)) compose1))

(module+ test
  (require (only-in (submod "pcf.rkt" test) fact-5))

  (check-equal?  (car ((repeated -->vσ*) (injσ fact-5))) (set 120)))

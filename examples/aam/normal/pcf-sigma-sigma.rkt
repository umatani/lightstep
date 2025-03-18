#lang racket/base
(require lightstep/base lightstep/syntax lightstep/inference
         (only-in "pcf.rkt" δ)
         (only-in "pcf-rho.rkt" vρ-rules)
         (only-in "pcf-varsigma.rkt" -->vς-rules)
         (only-in "pcf-sigma.rkt" [PCFσ orig-PCFσ] injσ alloc))
(provide -->vσ/Σ-rules)

(module+ test (require rackunit))

;;-----------------------------------------------------------------------------
;; 4.1 Abstracting over Σ (PCFσ)

(define-language PCFσ #:super orig-PCFσ)

;; σ --> σ
(define-inference (-->vσ/Σ-rules alloc ext-Σ lookup-Σ)
  #:do [;; (α ↦ β) List(α) List(β) → (α ↦ β)
        (define (ext m ks vs)
          (foldr (λ (k v m) (m k v)) m ks vs))
        ;; (α ↦ β) α → β
        (define (lookup m k) (m k))

        (define-inference (-->vς′-rules) #:super [(-->vς-rules)]
          #:do [;; remove rules manually
                (define-inference (vρ′-rules) #:super [(vρ-rules)]
                  [#:when #f
                   --------------- "ρ-x"
                   `(,x → ,(void))        ]
                  [#:when #f
                   --------------- "β"
                   `(,x → ,(void))        ]
                  [#:when #f
                   --------------- "rec-β"
                   `(,x → ,(void))        ])
                (define rvρ′ (reducer-of (vρ′-rules)))]
          #:forms (.... [`(,i →vρ′ ,o) #:where o ← (rvρ′ i)])

          ; Apply
          [`(,C →vρ′ ,C′)
           ---------------------- "ap"
           `((,C ,K) → (,C′ ,K))      ])

        (define rvς′ (reducer-of (-->vς′-rules)))]

  #:forms (.... [`(,i →vς′ ,o) #:where o ← (rvς′ i)])

  [`(,ς →vς′ ,ς′)
   ----------------------------- "ap"
   `((,(? ς? ς) ,Σ) →  (,ς′ ,Σ))     ]

  [--------------- "discard-Σ-N"
   `((,N ,Σ) → ,N)              ]

  [--------------- "discard-Σ-O"
   `((,O ,Σ) → ,O)              ]

  [A ≔ (lookup ρ X)        V ≔ (lookup-Σ Σ A)
     ------------------------------------------ "ρ-x"
     `((((,X ,(? ρ? ρ)) ,K) ,Σ) → ((,V ,K) ,Σ))      ]

  [`(,A ...) ≔ (alloc σ)
   ----------------------------------------------------------------- "β"
   `(,(and σ `(((((λ ([,X : ,T] ...) ,M) ,(? ρ? ρ)) ,V ...) ,K) ,Σ))
     → (((,M ,(ext ρ `(,X) `(,A))) ,K) ,(ext-Σ Σ `(,A) `(,V))))                        ]

  [`(,Aₐ ,A ...) ≔ (alloc σ)
   ------------------------------------------------------------------- "rec-β"
   `(,(and σ `(((,(and f `((μ [,Xₐ : ,Tₐ]
                              (λ ([,X : ,T] ...) ,M)) ,(? ρ? ρ))) ,V ...)
                ,K) ,Σ))
     → (((,M ,(ext ρ (cons Xₐ X) (cons Aₐ A))) ,K)
        ,(ext-Σ Σ (cons Aₐ A) (cons f V))))                                   ])

;; σ --> σ
(define-inference (-->vσ/alloc-rules alloc) #:super
  [(-->vσ/Σ-rules alloc ext lookup)])

;; σ → 𝒫(σ)
(define -->vσ (call-with-values (λ () (-->vσ/alloc-rules alloc)) compose1))

(module+ test
  (require (only-in (submod "pcf.rkt" test) fact-5))

  (check-equal?  (car ((repeated -->vσ) (injσ fact-5))) (set 120)))

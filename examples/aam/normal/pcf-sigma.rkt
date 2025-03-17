#lang racket/base
(require lightstep/base lightstep/syntax lightstep/inference
         (only-in "pcf.rkt" δ)
         (only-in "pcf-rho.rkt" vρ-rules)
         (only-in "pcf-varsigma.rkt" PCFς -->vς-rules injς))
(provide PCFσ -->vσ-rules injσ formals alloc)

(module+ test (require rackunit))

;;-----------------------------------------------------------------------------
;; 3.8 Heap-allocated bindings

(define-language PCFσ #:super PCFς
  ; [ρ ∷= (? map? X→A)] range changed
  [Σ ∷= (? map? A→V)]
  [A ∷= (? (λ (_) #t) any)]
  [σ ∷= `(,(? ς?) ,Σ) V])

;; σ --> σ
(define-inference (-->vσ-rules)
  #:do [(define (ext m ks vs)
          (foldr (λ (k v m) (m k v)) m ks vs))

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

  [A ≔ (ρ X)        V ≔ (Σ A)
   ------------------------------------------ "ρ-x"
   `((((,X ,(? ρ? ρ)) ,K) ,Σ) → ((,V ,K) ,Σ))      ]

  [`(,A ...) ≔ (alloc σ)
   ----------------------------------------------------------------- "β"
   `(,(and σ `(((((λ ([,X : ,T] ...) ,M) ,(? ρ? ρ)) ,V ...) ,K) ,Σ))
     → (((,M ,(ext ρ X A)) ,K) ,(ext Σ A V)))                          ]

  [`(,Aₐ ,A ...) ≔ (alloc σ)
   ------------------------------------------------------------------- "rec-β"
   `(,(and σ `(((,(and f `((μ [,Xₐ : ,Tₐ]
                            (λ ([,X : ,T] ...) ,M)) ,(? ρ? ρ))) ,V ...)
              ,K) ,Σ))
     → (((,M ,(ext ρ (cons Xₐ X) (cons Aₐ A))) ,K)
        ,(ext Σ (cons Aₐ A) (cons f V))))                                     ])

;; σ → 𝒫(σ)
(define -->vσ (call-with-values (λ () (-->vσ-rules)) compose1))

;; M → σ
(define (injσ M)
  `(,(injς M) ,(↦)))

;; M → (X ...)
(define (formals M)
  (match M
    [`(λ ([,X : ,T] ...) ,M)
     `(,@X)]
    [`(μ [,Xₐ : ,Tₐ] ,L)
     (match-let ([`(,X ...) (formals L)])
       `(,Xₐ ,@X))]))

;; σ → ([X X] ...)
(define/match (alloc σ)
  [`((((,M ,(? ρ?)) ,V ...) ,K) ,Σ)
   (map (λ (x) (list x (gensym x))) (formals M))])

(module+ test
  (require (only-in (submod "pcf.rkt" test) fact-5))

  ;(alloc `(((((λ ([y : num] [z : num]) y) ,(↦)) 5 7) []) ,(↦)))
  ;(-->vσ `(((((λ ([y : num] [z : num]) y) ,(↦)) 5 7) []) ,(↦)))

  (check-equal?  (car ((repeated -->vσ) (injσ fact-5))) (set 120)))

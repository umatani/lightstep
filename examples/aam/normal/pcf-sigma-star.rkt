#lang racket/base
(require lightstep/base lightstep/syntax lightstep/inference
         (only-in "pcf.rkt" δ)
         (only-in "pcf-rho.rkt" vρ-rules)
         (only-in "pcf-varsigma.rkt" -->vς-rules)
         (only-in "pcf-sigma.rkt" PCFσ injσ formals alloc)
         (only-in "pcf-sigma-alloc.rkt"-->vσ/alloc-rules))
(provide PCFσ* alloc*)

(module+ test (require rackunit))

;;-----------------------------------------------------------------------------
;; 3.10 Heap-allocated continuations

(define-language PCFσ* #:super PCFσ
  [K ∷= '() `(,F ,A)]
  ; [Σ ∷= (? map? A→U)] range changed
  [U ∷= V K])

;; σ → ([(X ∪ F) X] ...)
(define/match (alloc* σ) #:super alloc
  [`(((if0 ,S₀ ,C₁ ,C₂) ,K) ,Σ)
   `(((if0 □ ,C₁ ,C₂) ,(gensym 'if0)))]
  [`(((,V ... ,S ,C ...) ,K) ,Σ)
   `(((,@V □ ,@C) ,(gensym 'app)))])

(module+ test
  ;; (alloc* `(((if0 ((add1 2) ,(↦)) (3 ,(↦)) (4 ,(↦))) ()) ,(↦)))
  ;; (alloc* `(((((λ ([y : num]) y) ,(↦)) ((add1 2) ,(↦))) ()) ,(↦)))
  ;; (alloc* `(((((λ ([y : num] [z : num]) y) ,(↦)) 5 7) ()) ,(↦)))
  )

;; σ --> σ
(define-inference (-->vσ*/alloc-rules alloc*)
  #:super [(-->vσ/alloc-rules alloc*)]
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
   ------------------------------------------ "ev-if"
   `(,(and σ `(((if0 ,S₀ ,C₁ ,C₂) ,K) ,Σ))
     → ((,S₀ ((if0 □ ,C₁ ,C₂) ,A)) ,(Σ A K)))        ]

  [`(,A) ≔ (alloc* σ)
   ---------------------------------------- "ev-app"
   `(,(and σ `(((,V ... ,S ,C ...) ,K) ,Σ))
     → ((,S ((,@V □ ,@C) ,A)) ,(Σ A K)))            ]

  ; Continue
  [K ≔ (Σ A)
   -------------------------------- "co-if"
   `(((,V ((if0 □ ,C₁ ,C₂) ,A)) ,Σ)
     → (((if0 ,V ,C₁ ,C₂) ,K) ,Σ))         ]

  [K ≔ (Σ A)
   ------------------------------------ "co-app"
   `(((,V ((,V₀ ... □ ,C₀ ...) ,A)) ,Σ)
     → (((,@V₀ ,V ,@C₀) ,K) ,Σ))                ])

;; σ → 𝒫(σ)
(define -->vσ* (call-with-values (λ () (-->vσ*/alloc-rules alloc*)) compose1))
(define -->>vσ* (compose1 car (repeated -->vσ*)))

(module+ test
  (require (only-in (submod "pcf.rkt" test) fact-5))

  (check-equal? (-->>vσ* (injσ '((λ ([f : (num → num)])
                                   ((λ ([_ : num]) (f 0)) (f 1)))
                                 (λ ([z : num]) z)))) (set 0))

  (check-equal? (-->>vσ* (injσ fact-5)) (set 120)))

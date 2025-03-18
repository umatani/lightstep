#lang racket/base
(require lightstep/base lightstep/syntax lightstep/inference
         (only-in "pcf.rkt" δ)
         (only-in "pcf-rho.rkt" vρ-rules)
         (only-in "pcf-varsigma.rkt" -->vς-rules)
         (only-in "pcf-sigma.rkt" injσ formals)
         (only-in "pcf-sigma-star.rkt" PCFσ* [alloc* orig-alloc*])
         (only-in "pcf-sigma-star-sigma.rkt" -->vσ*/Σ-rules)
         (only-in "pcf-sigma-o.rkt" [lookup-Σ-rules orig-lookup-Σ-rules] ext-Σ))

(module+ test (require rackunit))

;;-----------------------------------------------------------------------------
;; 4.3 Make it finite

(define-language PCFσ^ #:super PCFσ*
  [N ∷= .... 'num])

;; M → N
(define/match (δ^ m)
  [`(,O ,N₀ ,N₁) 'num]
  [`(,O ,N)      'num])

;; re-interpret N
;; σ → ([(X ∪ F) X] ...)
(define/match (alloc* σ) #:super orig-alloc*)

;; re-interpret N
(define-inference (lookup-Σ-rules) #:super [(orig-lookup-Σ-rules)])

;; σ → ((X ∪ F) ...)
(define (alloc^ σ)
  (define Σ (cadr σ))
  (match (alloc* σ)
    [`([,A ,_] ...) A]))

;; δ --> δ
(define-inference (-->vσ^-rules)
  #:super [(-->vσ*/Σ-rules alloc^ ext-Σ (reducer-of (lookup-Σ-rules)))]

  #:do [(define-inference (-->vς‴-rules) #:super [(-->vς″-rules)]
          #:do [;; remove rules manually
                (define-inference (vρ″-rules) #:super [(vρ′-rules)]
                  [#:when #f
                   --------------- "δ" ;; NEW
                   `(,x → ,(void))        ])
                (define rvρ″ (reducer-of (vρ″-rules)))]
          #:forms (.... [`(,i →vρ″ ,o) #:where o ← (rvρ″ i)])

          ; override with →vρ′
          [`(,C →vρ″ ,C′)
           ---------------------- "ap"
           `((,C ,K) → (,C′ ,K))      ])

        (define rvς‴ (reducer-of (-->vς‴-rules)))]
  
  #:forms (.... [`(,i →vς‴ ,o) #:where o ← (rvς‴ i)])

  ;; override with →vς‴
  [`(,ς →vς‴ ,ς′)
   ----------------------------- "ap"
   `((,(? ς? ς) ,Σ) →  (,ς′ ,Σ))     ]

  [---------------------------------------------------- "δ"
   `((((,O ,N ...) ,K) ,Σ) → ((,(δ^ `(,O ,@N)) ,K) ,Σ))    ]

  [---------------------------------------------- "if0-num-t"
   `((((if0 num ,C₁ ,C₂) ,K) ,Σ) → ((,C₁ ,K) ,Σ))            ]

  [---------------------------------------------- "if0-num-f"
   `((((if0 num ,C₁ ,C₂) ,K) ,Σ) → ((,C₂ ,K) ,Σ))            ])

;; σ → 𝒫(σ)
(define -->vσ^ (call-with-values (λ () (-->vσ^-rules)) compose1))
(define -->>vσ^ (compose1 car (repeated -->vσ^)))

(module+ test
  (require (only-in (submod "pcf.rkt" test) fact-5 Ω))

  (check-equal? (-->>vσ^ (injσ '(if0 (add1 0) 1 2))) (set 1 2))
  
  (check-equal? (-->>vσ^ (injσ fact-5)) (set 1 'num))

  (check-equal? (-->>vσ^ (injσ '((λ ([f : (num → num)])
                                   ((λ ([_ : num]) (f 0)) (f 1)))
                                 (λ ([z : num]) z)))) (set 0 1))

  (check-equal? (-->>vσ^ (injσ Ω)) ∅))

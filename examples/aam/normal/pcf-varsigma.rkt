#lang racket/base
(require lightstep/base lightstep/syntax lightstep/inference
         (only-in "pcf.rkt" δ)
         (only-in "pcf-rho.rkt" PCFρ vρ-rules injρ))
(provide PCFς -->vς-rules injς)

(module+ test (require rackunit))

;;-----------------------------------------------------------------------------
;; 3.7 Eval/Continue/Apply machine

(define-language PCFς #:super PCFρ
  [F ∷=
     `(,V ... □ ,C ...)
     `(if0 □ ,C₁ ,C₂)]
  [K ∷= `[,F ...]]
  [S ∷= ; serious terms S ∩ V = ∅, C = S ∪ V
     `(,N ,(? ρ?))
     `(,O ,(? ρ?))
     `(,X ,(? ρ?))
     `((,M ,M′ ...) ,(? ρ?))
     `((if0 ,M₀ ,M₁ ,M₂) ,(? ρ?))
     `(if0 ,C₀ ,C₁ ,C₂)
     `(,C ,C′ ...)]
  [ς ∷= `(,C ,K) V])

;; ς --> ς
(define-inference (-->vς-rules)
  #:do [(define-reduction (rules) #:super [(vρ-rules)])
        (define rvρ (reducer-of (rules)))]
  #:forms (.... [`(,i →vρ ,o) #:where o ← (rvρ i)])

  ; Apply
  [`(,C →vρ ,C′)
   ---------------------- "ap"
   `((,C ,K) → (,C′ ,K))      ]

  ; Eval
  [-------------------------------- "ev-if"
   `(((if0 ,S₀ ,C₁ ,C₂) [,F ...])
     → (,S₀ [(if0 □ ,C₁ ,C₂) ,@F]))        ]

  [------------------------------- "ev-app"
   `(((,V ... ,S ,C ...) [,F ...])
     → (,S [(,@V □ ,@C) ,@F]))             ]

  ; Continue
  [--------------- "halt"
   `((,V []) → ,V)       ]

  [------------------------------- "co-if"
   `((,V [(if0 □ ,C₁ ,C₂) ,F ...])
     → ((if0 ,V ,C₁ ,C₂) [,@F]))          ]

  [----------------------------------- "co-app"
   `((,V [(,V₀ ... □ ,C₀ ...) ,F ...])
     → ((,@V₀ ,V ,@C₀) [,@F]))                 ])

;; ς → 𝒫(ς)
(define -->vς (call-with-values (λ () (-->vς-rules)) compose1))

;; M → ς
(define (injς M)
  `(,(injρ M) []))

(module+ test
  (require (only-in (submod "pcf.rkt" test) fact-5))
  (check-equal? (car ((repeated -->vς) (injς fact-5)))
                (set 120))
  (check-equal? (car ((repeated -->vς)
                      (injς '((λ ([x : num]) x) (add1 5)))))
                (set 6)))

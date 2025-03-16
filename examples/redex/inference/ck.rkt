#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/transformers
         lightstep/inference
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" ISWIM FV subst δ))

(module+ test (require rackunit))

;;=============================================================================
;; 6.3 The CK Machine

(define-language CK #:super ISWIM
  [κ ∷=
     'mt
     `(fn ,V ,(? κ? κ))
     `(ar ,M ,(? κ? κ))
     `(op ,(? list? VsOⁿ) ,(? list? Ns) ,(? κ? κ))])

(define-inference (⊢->ck-rules)
  #:monad (StateT #f (NondetT ID))

  [(? κ? κ) ← get
   (put `(ar ,M₂ ,κ))
   ------------------ "ck1"
   `((,M₁ ,M₂) → ,M₁)      ]

  [(? κ? κ) ← get
   (put `(op (,oⁿ) (,@M′) ,κ))
   -------------------------------- "ck2"
   `((,(? oⁿ? oⁿ) ,M ,M′ ...) → ,M)      ]

  [`(fn (λ ,X ,M) ,(? κ? κ)) ← get
   (put κ)
   ------------------------------- "ck3"
   `(,V → ,(subst M X V))               ]

  [`(ar ,M ,(? κ? κ)) ← get
   (put `(fn ,V ,κ))
   ------------------------ "ck4"
   `(,V → ,M)                    ]

  [`(op (,(? b? b) ... ,oⁿ) () ,(? κ? κ)) ← get
   (put κ)
   -------------------------------------------------- "ck5"
   `(,(? b? bₙ) → ,(δ oⁿ `(,@(reverse (cons bₙ b)))))      ]

  [`(op (,V′ ... ,oⁿ) (,M ,M′ ...) ,(? κ? κ)) ← get
   (put `(op (,V ,@V′ ,oⁿ) (,@M′) ,κ))
   ------------------------------------------------ "ck6"
   `(,V → ,M)                                            ])

(define-match-expander mkCK
  (syntax-parser
    [(_ M κ) #'(cons M κ)])
  (syntax-parser
    [(_ M κ) #'(cons M κ)]))

(define ⊢->ck (let-values ([(mrun reducer) (⊢->ck-rules)])
                (match-λ
                 [(mkCK M (? κ? κ))
                  (mrun κ (reducer M))])))
(define ⊢->>ck (compose1 car (repeated ⊢->ck)))

(define/match (evalck m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>ck (mkCK M 'mt))
     [(set (mkCK (? b? b) 'mt))
      b]
     [(set (mkCK `(λ ,X ,M) 'mt))
      'function]
     [x (error 'evalck "invalid final state: ~s" x)])]
  [_ (error 'evalck "invalid input: ~s" m)])

(module+ test
  (require (only-in (submod "cc.rkt" test) Ω))

  (check-equal? (⊢->>ck (mkCK '(((λ x x) (λ y y)) 1) 'mt))
                (set (cons 1 'mt)))
  (check-equal? (⊢->>ck (mkCK '(+ (add1 2) (* 3 4)) 'mt))
                (set (cons 15 'mt)))

  (check-equal? (evalck '(+ (* 9 (↑ 2 3)) 3)) 75)
  (check-equal? (evalck '(((λ f (λ x (f x))) (λ y (+ y y))) 8)) 16)

  (check-equal? (⊢->>ck (mkCK Ω 'mt)) ∅))

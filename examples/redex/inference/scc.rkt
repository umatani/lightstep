#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/transformers
         lightstep/inference
         (only-in "iswim.rkt" [ISWIM orig-ISWIM] FV subst δ)
         (only-in "cc.rkt" ECxt □))

(module+ test (require rackunit))

(define-language ISWIM #:super orig-ISWIM)

;;=============================================================================
;; 6.2 The CC Machine

;; (M ECxt) --> (M ECxt)
(define-inference (⊢->scc-rules)
  #:monad (StateT #f (NondetT ID))

  [(ECxt (□)) ← get
   (put (ECxt `(,(□) ,M₂)))
   ------------------------ "scc1"
   `((,M₁ ,M₂) → ,M₁)             ]

  [(ECxt (□)) ← get
   (put (ECxt `(,oⁿ ,(□) ,@M)))
   --------------------------------- "scc2"
   `((,(? oⁿ? oⁿ) ,M₁ ,M ...) → ,M₁)       ]

  [(ECxt `((λ ,X ,M) ,(□))) ← get
   (put (ECxt (□)))
   ------------------------------ "scc3"
   `(,V → ,(subst M X V))               ]

  [(ECxt `(,(□) ,M)) ← get
   (put (ECxt `(,V ,(□))))
   ----------------------- "scc4"
   `(,V → ,M)                    ]

  [(ECxt `(,(? oⁿ? oⁿ) ,(? b? b) ... ,(□))) ← get
   (put (ECxt (□)))
   ---------------------------------------------- "scc5"
   `(,(? b? bₙ) → ,(δ oⁿ `(,@b ,bₙ)))                   ]

  [(ECxt `(,(? oⁿ? oⁿ) ,V₁ ... ,(□) ,M₁ ,M ...)) ← get
   (put (ECxt `(,oⁿ ,@V₁ ,V ,(□) ,@M)))
   --------------------------------------------------- "scc6"
   `(,V → ,M₁)                                               ])

(define-match-expander mkSCC
  (syntax-parser
    [(_ M ECxt) #'(cons M ECxt)])
  (syntax-parser
    [(_ M ECxt) #'(cons M ECxt)]))

;; (M ECxt) → 𝒫((M ECxt))
(define ⊢->scc (let-values ([(mrun reducer) (⊢->scc-rules)])
                 (match-λ
                  [(mkSCC M ECxt)
                   (mrun ECxt (reducer M))])))
(define ⊢->>scc (compose1 car (repeated ⊢->scc)))

;; M → V
(define/match (evalscc m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>scc (mkSCC M (□)))
     [(set (mkSCC (? b? b) (□)))
      b]
     [(set (mkSCC `(λ ,X ,M) (□)))
      'function]
     [x (error 'evalscc "invalid final state: ~s" x)])]
  [_ (error 'evalscc "invalid input: ~s" m)])

(module+ test
  (require (only-in (submod "cc.rkt" test) Ω))

  (check-equal? (⊢->>scc (mkSCC '(((λ x x) (λ y y)) 1) (□)))
                (set (cons 1 (□))))
  (check-equal? (⊢->>scc (mkSCC '(+ (add1 2) (* 3 4)) (□)))
                (set (cons 15 (□))))

  (check-equal? (evalscc '(+ (* 9 (↑ 2 3)) 3)) 75)
  (check-equal? (evalscc '(((λ f (λ x (f x))) (λ y (+ y y))) 8)) 16)

  (check-equal? (⊢->>scc (mkSCC Ω (□))) ∅))

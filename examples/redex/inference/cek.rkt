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

(define-inference (⊢->cek-rules)
  #:monad (StateT #f (StateT #f (NondetT ID)))
  #:do [(define get-E (bind get (compose1 return car)))
        (define get-κ (bind get (compose1 return cdr)))
        (define (put-E E)
          (do (cons _ κ) ← get
              (put (cons E κ))))
        (define (put-κ κ)
          (do (cons E _) ← get
              (put (cons E κ))))]
  [E ← get-E
   κ ← get-κ
   (put-κ `(ar (,M₂ ,E) ,κ))
   ------------------------- "cek1"
   `((,M₁ ,M₂) → ,M₁)              ]

  [E ← get-E
   κ ← get-κ
   (put-κ `(op (,oⁿ) ,(map (λ (m) `(,m ,E)) M′) ,κ))
   ------------------------------------------------- "cek2"
   `((,(? oⁿ? oⁿ) ,M ,M′ ...) → ,M)                        ]

  [#:when (not (X? V))
   E ← get-E
   `(fn ((λ ,X₁ ,M) ,E′) ,κ) ← get-κ
   (put-E (E′ X₁ `(,V ,E)))
   (put-κ κ)
   --------------------------------- "cek3"
   `(,V → ,M)                              ]

  [#:when (not (X? V))
   E ← get-E
   `(ar (,M ,E′) ,κ) ← get-κ
   (put-E E′)
   (put-κ `(fn (,V ,E) ,κ))
   ------------------------- "cek4"
   `(,V → ,M)                      ]

  [`(op ((,(? b? b) ,_) ... ,oⁿ) () ,κ) ← get-κ
   (put-E (↦))
   (put-κ κ)
   --------------------------------------------- "cek5"
   `(,(? b? bₙ) → ,(δ oⁿ (reverse (cons bₙ b))))       ]

  [#:when (not (X? V))
   E ← get-E
   `(op (,c ... ,oⁿ) ((,M ,Eₘ) ,cₗ ...) ,κ) ← get-κ
   (put-E Eₘ)
   (put-κ `(op ((,V ,E) ,@c ,oⁿ) (,@cₗ) ,κ))
   ------------------------------------------------ "cek6"
   `(,V → ,M)                                             ]

  [(↦ [x `(,V ,E′)]) ← get-E
   (put-E E′)
   ------------------------- "cek7"
   `(,(? X? x) → ,V)               ])

(define-match-expander mkCEK
  (syntax-parser
    [(_ M E κ) #'(cons (cons M E) κ)])
  (syntax-parser
    [(_ M E κ) #'(cons (cons M E) κ)]))

(define ⊢->cek (let-values ([(mrun reducer) (⊢->cek-rules)])
                 (match-λ
                  [(mkCEK M E (? κ? κ))
                   (mrun κ E (reducer M))])))
(define ⊢->>cek (compose1 car (repeated ⊢->cek)))

(define/match (evalcek m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>cek (mkCEK M (↦) 'mt))
     [(set (mkCEK (? b? b) E 'mt))
      b]
     [(set (mkCEK `(λ ,X ,M) E 'mt))
      'function]
     [x (error 'evalcek "invalid final state: ~a" x)])]
  [_ (error 'evalcek "invalid input: ~a" m)])

(module+ test
  (require (only-in (submod "cc.rkt" test) Ω))
  
  (check-equal? (evalcek '(+ (* 9 (↑ 2 3)) 3)) 75)
  (check-equal? (evalcek '(((λ f (λ x (f x))) (λ y (+ y y))) 8)) 16)

  (check-equal? (⊢->>cek (mkCEK Ω (↦) 'mt)) ∅))

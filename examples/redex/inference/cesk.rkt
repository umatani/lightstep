#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/transformers
         lightstep/inference
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" δ)
         (only-in "s-iswim.rkt" S-ISWIM FV))
(provide CESK ⊢->cesk-rules mkCESK)

(module+ test (require rackunit))

;;=============================================================================
;; 9.4 The CESK Machine

(define-language CESK #:super S-ISWIM
  [σ ∷= (? symbol?)]
  [E ∷= (? map? X→σ)]
  [Σ ∷= (? map? σ→VE)]
  [κ ∷=
     'mt
     `(fn (,V ,E) ,(? κ?))
     `(ar (,M ,E) ,(? κ?))
     `(op ,(? list? VEsOⁿ) ,(? list? MEs) ,(? κ?))
     `(set ,(? σ?) ,(? κ?))])

;; (M E Σ κ) --> (M E Σ κ)
(define-inference (⊢->cesk-rules)
  #:monad (StateT #f (StateT #f (NondetT ID)))
  #:do [(define get-Σ (bind get (compose1 return car)))
        (define get-κ (bind get (compose1 return cdr)))
        (define (put-Σ Σ)
          (do `(,_ . ,κ) ← get
              (put `(,Σ . ,κ))))
        (define (put-κ κ)
          (do `(,Σ . ,_) ← get
              (put `(,Σ . ,κ))))]

  [κ ← get-κ
   (put-κ `(ar (,M₂ ,E) ,κ))
   ---------------------------- "cesk1"
   `(((,M₁ ,M₂) ,E) → (,M₁ ,E))        ]

  [κ ← get-κ
   (put-κ `(op (,oⁿ) ,(map (λ (m) `(,m ,E)) M) ,κ))
   ------------------------------------------------ "cesk2"
   `(((,(? oⁿ? oⁿ) ,M₁ ,M ...) ,E) → (,M₁ ,E))             ]
  
  [#:when (not (X? V))
   `(fn ((λ ,X ,M) ,E′) ,κ) ← get-κ
   Σ ← get-Σ
   σ ≔ ((symbol-not-in (dom Σ)) X)
   (put-Σ (Σ σ `(,V ,E)))
   (put-κ κ)
   -------------------------------- "cesk3"
   `((,V ,E) → (,M ,(E′ X σ)))             ]

  [#:when (not (X? V))
   `(ar (,M ,E′) ,κ) ← get-κ
   (put-κ `(fn (,V ,E) ,κ))
   ------------------------- "cesk4"
   `((,V ,E) → (,M ,E′))            ]

  [`(op ((,(? b? b) ,E′) ... ,(? oⁿ? oⁿ)) () ,κ) ← get-κ
   (put-κ κ)
   --------------------------------------------------------- "cesk5"
   `((,(? b? bₙ) ,E) → (,(δ oⁿ (reverse (cons bₙ b))) ,(↦)))        ]

  [#:when (not (X? V))
   `(op (,c ... ,oⁿ) ((,M ,Eₘ) ,c′ ...) ,κ) ← get-κ
   (put-κ `(op ((,V ,E) ,@c ,oⁿ) (,@c′) ,κ))
   ------------------------------------------------ "cesk6"
   `((,V ,E) → (,M ,Eₘ))                                   ]
  
  [Σ ← get-Σ
   `(,V ,E′) ≔ (Σ (E X))
   --------------------- "cesk7"
   `((,X ,E) → (,V ,E′))        ]

  [κ ← get-κ
   (put-κ `(set ,(E X) ,κ))
   ----------------------------- "cesk8"
   `(((set ,X ,M) ,E) → (,M ,E))        ]

  [#:when (not (X? V))
   `(set ,σ ,κ) ← get-κ
   Σ ← get-Σ
   `(,V′ ,E′) ≔ (Σ σ)
   (put-Σ (Σ σ `(,V ,E)))
   (put-κ κ)
   ---------------------- "cesk9"
   `((,V ,E) → (,V′ ,E′))        ])

(define-match-expander mkCESK
  (syntax-parser
    [(_ C E S K) #'(cons (cons `(,C ,E) S) K)])
  (syntax-parser
    [(_ C E S K) #'(cons (cons `(,C ,E) S) K)]))

;; (M E Σ κ) → 𝒫((M E Σ κ))
(define ⊢->cesk (let-values ([(mrun reducer) (⊢->cesk-rules)])
                  (match-λ
                   [(mkCESK M E Σ (? κ? κ))
                    (mrun κ Σ (reducer `(,M ,E)))])))
(define ⊢->>cesk (compose1 car (repeated ⊢->cesk)))

;; M → V
(define/match (evalcesk m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>cesk (mkCESK M (↦) (↦) 'mt))
     [(set (mkCESK (? b? b) E Σ 'mt))
      b]
     [(set (mkCESK `(λ ,X ,M) E Σ 'mt))
      'function]
     [x (error 'evalcesk "invalid final state: ~s" x)])]
  [_ (error 'evalcesk "invalid input: ~s" m)])

(module+ test
  (require (only-in "cs.rkt" LET SEQ))

  (check-equal? (evalcesk `((λ x ,(SEQ '(set x (* x x)) '(add1 x))) 8)) 65)
  (check-equal? (evalcesk (LET '([x 0])
                               (SEQ '(set x 5)
                                    (LET '([x 9]) (SEQ '(set x (+ x x))
                                                       'x)))))
                18))

#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/transformers
         lightstep/inference
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" δ)
         (only-in "s-iswim.rkt" S-ISWIM FV))
(provide CESK ⊢->cesk mkCESK)

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

(define-inference (⊢->cesk)
  #:monad (StateT #f (StateT #f (StateT #f (NondetT ID))))
  #:do [(define get-E (bind get (compose1 return car)))
        (define get-Σ (bind get (compose1 return cadr)))
        (define get-κ (bind get (compose1 return cddr)))
        (define (put-E E)
          (do `(,_ ,Σ . ,κ) ← get
              (put `(,E ,Σ . ,κ))))
        (define (put-Σ Σ)
          (do `(,E ,_ . ,κ) ← get
              (put `(,E ,Σ . ,κ))))
        (define (put-κ κ)
          (do `(,E ,Σ . ,_) ← get
              (put `(,E ,Σ . ,κ))))]

  [E ← get-E    κ ← get-κ
   (put-κ `(ar (,M₂ ,E) ,κ))
   ------------------------- "cesk1"
   `((,M₁ ,M₂) → ,M₁)               ]

  [E ← get-E    κ ← get-κ
   (put-κ `(op (,oⁿ) ,(map (λ (m) `(,m ,E)) M) ,κ))
   ------------------------------------------------ "cesk2"
   `((,(? oⁿ? oⁿ) ,M₁ ,M ...) → ,M₁)                       ]
  
  [#:when (not (X? V))
   E ← get-E    Σ ← get-Σ
   `(fn ((λ ,X ,M) ,E′) ,κ) ← get-κ
   σ ≔ ((symbol-not-in (dom Σ)) X)
   (put-E (E′ X σ))
   (put-Σ (Σ σ `(,V ,E)))
   (put-κ κ)
   -------------------------------- "cesk3"
   `(,V → ,M)                              ]

  [#:when (not (X? V))
   E ← get-E
   `(ar (,M ,E′) ,κ) ← get-κ
   (put-E E′)
   (put-κ `(fn (,V ,E) ,κ))
   ------------------------- "cesk4"
   `(,V → ,M)                       ]

  [`(op ((,(? b? b) ,_) ... ,(? oⁿ? oⁿ)) () ,κ) ← get-κ
   (put-E (↦))    (put-κ κ)
   ---------------------------------------------------- "cesk5"
   `(,(? b? bₙ) → ,(δ oⁿ (reverse (cons bₙ b))))               ]

  [#:when (not (X? V))
   E ← get-E
   `(op (,c ... ,oⁿ) ((,M ,Eₘ) ,c′ ...) ,κ) ← get-κ
   (put-E Eₘ)
   (put-κ `(op ((,V ,E) ,@c ,oⁿ) (,@c′) ,κ))
   ------------------------------------------------ "cesk6"
   `(,V → ,M)                                              ]
  
  [E ← get-E    Σ ← get-Σ
   `(,V ,E′) ≔ (Σ (E X))
   (put-E E′)
   ---------------------- "cesk7"
   `(,X → ,V)                    ]

  [E ← get-E    κ ← get-κ
   (put-κ `(set ,(E X) ,κ))
   ------------------------ "cesk8"
   `((set ,X ,M) → ,M)             ]

  [#:when (not (X? V))
   E ← get-E    Σ ← get-Σ
   `(set ,σ ,κ) ← get-κ
   `(,V′ ,E′) ≔ (Σ σ)
   (put-E E′)
   (put-Σ (Σ σ `(,V ,E)))
   (put-κ κ)
   ---------------------- "cesk9"
   `(,V → ,V′)
   ])

(define-match-expander mkCESK
  (syntax-parser
    [(_ C E S K) #'(cons (cons (cons C E) S) K)])
  (syntax-parser
    [(_ C E S K) #'(cons (cons (cons C E) S) K)]))

(define step⊢->cesk (let-values ([(mrun reducer) (⊢->cesk)])
                      (match-λ
                       [(mkCESK M E Σ (? κ? κ))
                        (mrun κ Σ E (reducer M))])))
(define ⊢->>cesk (compose1 car (repeated step⊢->cesk)))

(define/match (evalcesk m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>cesk (mkCESK M (↦) (↦) 'mt))
     [(set (mkCESK (? b? b) E Σ 'mt))
      b]
     [(set (mkCESK `(λ ,X ,M) E Σ 'mt))
      'function]
     [x (error 'evalcesk "invalid final state: ~a" x)])]
  [_ (error 'evalcesk "invalid input: ~a" m)])

(module+ test
  (require (only-in "cs.rkt" LET SEQ))

  (check-equal? (evalcesk `((λ x ,(SEQ '(set x (* x x)) '(add1 x))) 8)) 65)
  (check-equal? (evalcesk (LET '([x 0])
                               (SEQ '(set x 5)
                                    (LET '([x 9]) (SEQ '(set x (+ x x))
                                                       'x)))))
                18))

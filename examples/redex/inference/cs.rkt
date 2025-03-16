#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/transformers
         lightstep/inference
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" ISWIM [FV orig-FV] [subst orig-subst] δ))
(provide S-ISWIM AV FV subst E ⊢->cs-rules mkCS LET SEQ)

(module+ test (require rackunit))

;;=============================================================================
;; 9.2 The CS Machine

(define-language S-ISWIM #:super ISWIM
  [M ∷= .... `(set ,X ,M)]
  [Σ ∷= (? map? XVs)]
  [V ∷= (? b?) `(λ ,X ,M)])

(define/match (make-λ xs m)
  [('() M) M]
  [(`(,X ,X′ ...) M)
   `(λ ,X ,(make-λ X′ M))])

(define/match (make-app f vs)
  [(M '()) M]
  [(M `(,M₁ ... ,M′))
   `(,(make-app M M₁) ,M′)])

(define/match (LET bs n)
  [(`([,X ,M] ...) M′)
   (make-app (make-λ X M′) M)])

(define (SEQ . ms)
  (match ms
    [`(,M ..1)
     (match (build-list (length M) (λ (_) (gensym 'X)))
       [`(,X₁ ... ,Xₙ)
        (make-app (make-λ `(,@X₁ ,Xₙ) Xₙ) M)])]))

(module+ test
  (check-equal? (LET '([x 1] [y 2] [z 3]) '(* (+ x y) z))
                '((((λ x (λ y (λ z (* (+ x y) z)))) 1) 2) 3))
  ;;(SEQ '(set x 1) '(set y 2) '(set z 3))
  )


(define/match (AV m)
  [X                  ∅]
  [`(λ ,X ,M)         (set-remove (FV M) X)]
  [`(,M₁ ,M₂)         (∪ (AV M₁) (AV M₂))]
  [`(set ,X ,M)       (set-add (AV M) X)]
  [(? b?)             ∅]
  [`(,(? oⁿ?) ,M ...) (apply ∪ (map AV M))])

(define/match (FV m) #:super orig-FV
  [`(set ,X ,M)       (set-add (FV M) X)])

(define/match (subst m₁ x₂ m₂) #:super orig-subst
  [(`(set ,X ,M) X₂ X₂′)
   #:when (eq? X X₂)
   `(set ,X₂′ ,(subst M X₂ X₂′))]
  [(`(set ,X ,M) X₂ M₂)
   `(set ,X ,(subst M X₂ M₂))]
  )

(define-match-expander E
  (syntax-parser
    [(E p)
     #'(... (cxt E [□ p]
                 `(,V ,□)
                 `(,□ ,M)
                 `(,(? oⁿ?) ,V ... ,□ ,M ...)
                 `(set ,X ,□) ; NEW
                 ))]))

(define-inference (⊢->cs-rules)
  #:monad (StateT #f (NondetT ID))

  [#:when (not (∈ X (AV M)))
   -------------------------------------------- "csfiᵥ"
   `(,(E `((λ ,X ,M) ,V)) → ,(E (subst M X V)))        ]
  
  [#:when (∈ X (AV M))
   Σ ← get
   X′ ≔ ((symbol-not-in (dom Σ) (FV (E `(λ ,X ,M)))) X)
   (put (Σ X′ V))
   ---------------------------------------------------- "csfiₛ"
   `(,(E `((λ ,X ,M) ,V)) → ,(E (subst M X X′)))               ]

  [(↦ [x V]) ← get
   ------------------------- "cs!"
   `(,(E (? X? x)) → ,(E V))      ]

  [(and Σ (↦ [x V′])) ← get
   (put (Σ x V))
   ------------------------------------- "cs="
   `(,(E `(set ,(? X? x) ,V)) → ,(E V′))      ]

  [--------------------------------------------- "csffi"
   `(,(E `(,(? oⁿ? oⁿ) ,V ...)) → ,(E (δ oⁿ V)))        ])

(define-match-expander mkCS
  (syntax-parser
    [(_ M Σ) #'(cons M Σ)])
  (syntax-parser
    [(_ M Σ) #'(cons M Σ)]))

(define ⊢->cs (let-values ([(mrun reducer) (⊢->cs-rules)])
                (match-λ
                 [(mkCS M Σ)
                  (mrun Σ (reducer M))])))
(define ⊢->>cs (compose1 car (repeated ⊢->cs)))

(define/match (evalcs m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>cs (mkCS M (↦)))
     [(set (mkCS (? b? b) Σ))
      b]
     [(set (mkCS `(λ ,X ,M) Σ))
      'function]
     [x (error 'evalcs "invalid final state: ~s" x)])]
  [_ (error 'evalcs "invalid input: ~s" m)])

(module+ test
  (check-equal? (evalcs `((λ x ,(SEQ '(set x (* x x)) '(add1 x))) 8)) 65)
  (check-equal? (evalcs (LET '([x 0])
                             (SEQ '(set x 5)
                                  (LET '([x 9]) (SEQ '(set x (+ x x))
                                                     'x)))))
                18))

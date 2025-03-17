#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/transformers
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" ISWIM FV δ))
(provide CEK ⊢->cek mkCEK)

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

;; (M E κ) --> (M E κ)
(define-reduction (⊢->cek)
  #:monad (StateT #f (NondetT ID))

  [`((,M₁ ,M₂) ,E)
   κ ← get
   (put `(ar (,M₂ ,E) ,κ))
   `(,M₁ ,E)
   "cek1"]

  [`((,(? oⁿ? oⁿ) ,M ,M′ ...) ,E)
   κ ← get
   (put `(op (,oⁿ) ,(map (λ (m) `(,m ,E)) M′) ,κ))
   `(,M ,E)
   "cek2"]

  [`(,V ,E)
   #:when (not (X? V))
   `(fn ((λ ,X₁ ,M) ,E′) ,κ) ← get
   (put κ)
   `(,M ,(E′ X₁ `(,V ,E)))
   "cek3"]

  [`(,V ,E)
   #:when (not (X? V))
   `(ar (,M ,E′) ,κ) ← get
   (put `(fn (,V ,E) ,κ))
   `(,M ,E′)
   "cek4"]

  [`(,(? b? bₙ) ,E)
   `(op ((,(? b? b) ,_) ... ,oⁿ) () ,κ) ← get
   (put κ)
   `(,(δ oⁿ (reverse (cons bₙ b))) ,(↦))
   "cek5"]

  [`(,V ,E)
   #:when (not (X? V))
   `(op (,c ... ,oⁿ) ((,M ,Eₘ) ,cₗ ...) ,κ) ← get
   (put `(op ((,V ,E) ,@c ,oⁿ) (,@cₗ) ,κ))
   `(,M ,Eₘ)
   "cek6"]

  [`(,(? X? x) ,E)
   (↦ [x `(,V ,E′)]) ≔ E
   `(,V ,E′)
   "cek7"])

(define-match-expander mkCEK
  (syntax-parser
    [(_ M E κ) #'(cons `(,M ,E) κ)])
  (syntax-parser
    [(_ M E κ) #'(cons `(,M ,E) κ)]))

;; (M E κ) → 𝒫((M E κ))
(define step⊢->cek (let-values ([(mrun reducer) (⊢->cek)])
                     (match-λ
                      [(mkCEK M E (? κ? κ))
                       (mrun κ (reducer `(,M ,E)))])))
(define ⊢->>cek (compose1 car (repeated step⊢->cek)))

;; M → V
(define/match (evalcek m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>cek (mkCEK M (↦) 'mt))
     [(set (mkCEK (? b? b) E 'mt))
      b]
     [(set (mkCEK `(λ ,X ,M) E 'mt))
      'function]
     [x (error 'evalcek "invalid final state: ~s" x)])]
  [_ (error 'evalcek "invalid input: ~s" m)])

(module+ test
  (require (only-in (submod "cc.rkt" test) Ω))
  
  (check-equal? (evalcek '(+ (* 9 (↑ 2 3)) 3)) 75)
  (check-equal? (evalcek '(((λ f (λ x (f x))) (λ y (+ y y))) 8)) 16)

  (check-equal? (⊢->>cek (mkCEK Ω (↦) 'mt)) ∅))

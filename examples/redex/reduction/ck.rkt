#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/transformers
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

;; (M κ) --> (M κ)
(define-reduction (⊢->ck)
  #:monad (StateT #f (NondetT ID))

  [`(,M₁ ,M₂)
   (? κ? κ) ← get
   (put `(ar ,M₂ ,κ))
   M₁
   "ck1"]

  [`(,(? oⁿ? oⁿ) ,M ,M′ ...)
   (? κ? κ) ← get
   (put `(op (,oⁿ) (,@M′) ,κ))
   M
   "ck2"]

  [V
   `(fn (λ ,X ,M) ,(? κ? κ)) ← get
   (put κ)
   (subst M X V)
   "ck3"]

  [V
   `(ar ,M ,(? κ? κ)) ← get
   (put `(fn ,V ,κ))
   M
   "ck4"]

  [(? b? bₙ)
   `(op (,(? b? b) ... ,oⁿ) () ,(? κ? κ)) ← get
   (put κ)
   (δ oⁿ `(,@(reverse (cons bₙ b))))
   "ck5"]

  [V
   `(op (,V′ ... ,oⁿ) (,M ,M′ ...) ,(? κ? κ)) ← get
   (put `(op (,V ,@V′ ,oⁿ) (,@M′) ,κ))
   M
   "ck6"])

(define-match-expander mkCK
  (syntax-parser
    [(_ M κ) #'(cons M κ)])
  (syntax-parser
    [(_ M κ) #'(cons M κ)]))

;; (M κ) → 𝒫((M κ))
(define step⊢->ck (let-values ([(mrun reducer) (⊢->ck)])
                    (match-λ
                     [(mkCK M (? κ? κ))
                      (mrun κ (reducer M))])))
(define ⊢->>ck (compose1 car (repeated step⊢->ck)))

;; M → V
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

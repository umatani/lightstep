#lang racket/base
(require lightstep/base lightstep/syntax
         (only-in "iswim.rkt" FV δ)
         (only-in "cek.rkt" CEK ⊢->cek mkCEK))

(module+ test (require rackunit))

;;=============================================================================
;; Exercise 7.5  CEK with SS (Safe for Space)

(define-language CEK/SS #:super CEK)

(define-reduction (⊢->cek/ss) #:super [(⊢->cek)]
  [`((,M₁ ,M₂) ,E)
   κ ← get
   (put `(ar (,M₂ ,(restrict E (FV M₂))) ,κ))
   `(,M₁ ,E)
   "cek1"]

  [`((,(? oⁿ? oⁿ) ,M ,M′ ...) ,E)
   κ ← get
   (put `(op (,oⁿ) ,(map (λ (m) `(,m ,(restrict E (FV m)))) M′) ,κ))
   `(,M ,E)
   "cek2"]

  [`(,V ,E)
   #:when (not (X? V))
   `(ar (,M ,E′) ,κ) ← get
   (put `(fn (,V ,(restrict E (FV V))) ,κ))
   `(,M ,E′)
   "cek4"]

  [`(,V ,E)
   #:when (not (X? V))
   `(op (,c ... ,oⁿ) ((,M ,Eₘ) ,cₗ ...) ,κ) ← get
   (put `(op ((,V ,(restrict E (FV V))) ,@c ,oⁿ) (,@cₗ) ,κ))
   `(,M ,Eₘ)
   "cek6"])

(define step⊢->cek/ss (let-values ([(mrun reducer) (⊢->cek/ss)])
                        (match-λ
                         [(mkCEK M E (? κ? κ))
                          (mrun κ (reducer `(,M ,E)))])))
(define ⊢->>cek/ss (compose1 car (repeated step⊢->cek/ss)))

(define/match (evalcek/ss m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>cek/ss (mkCEK M (↦) 'mt))
     [(set (mkCEK (? b? b) E 'mt))
      b]
     [(set (mkCEK `(λ ,X ,M) E 'mt))
      'function]
     [x (error 'evalcek/ss "invalid final state: ~s" x)])]
  [_ (error 'evalcek/ss "invalid input: ~s" m)])

(module+ test
  (require (only-in (submod "cc.rkt" test) Ω))
  
  (check-equal? (evalcek/ss '(+ (* 9 (↑ 2 3)) 3)) 75)
  (check-equal? (evalcek/ss '(((λ f (λ x (f x))) (λ y (+ y y))) 8)) 16)

  (check-equal? (⊢->>cek/ss (mkCEK Ω (↦) 'mt)) ∅))

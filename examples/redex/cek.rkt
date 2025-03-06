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
     `(fn (,V ,ξ) ,(? κ? κ))
     `(ar (,M ,ξ) ,(? κ? κ))
     `(op ,(? list? VξsOⁿ) ,(? list? Mξs) ,(? κ? κ))]
  [E ∷= (? map? X→VE)])

(define-reduction (⊢->cek)
  #:monad (StateT #f (StateT #f (NondetT ID)))
  #:do [(define get-E (bind get (compose1 return car)))
        (define get-κ (bind get (compose1 return cdr)))
        (define (put-E E)
          (do (cons _ κ) ← get
              (put (cons E κ))))
        (define (put-κ κ)
          (do (cons E _) ← get
              (put (cons E κ))))]
  [`(,M₁ ,M₂)
   E ← get-E
   κ ← get-κ
   (put-κ `(ar (,M₂ ,E) ,κ))
   M₁
   "cek1"]

  [`(,(? oⁿ? oⁿ) ,M ,M′ ...)
   E ← get-E
   κ ← get-κ
   (put-κ `(op (,oⁿ) ,(map (λ (m) `(,m ,E)) M′) ,κ))
   M
   "cek2"]

  [V
   #:when (not (X? V))
   E ← get-E
   `(fn ((λ ,X₁ ,M) ,E′) ,κ) ← get-κ
   (put-E (E′ X₁ `(,V ,E)))
   (put-κ κ)
   M
   "cek3"]

  [V
   #:when (not (X? V))
   E ← get-E
   `(ar (,M ,E′) ,κ) ← get-κ
   (put-E E′)
   (put-κ `(fn (,V ,E) ,κ))
   M
   "cek4"]

  [(? b? bₙ)
   `(op ((,(? b? b) ,_) ... ,oⁿ) () ,κ) ← get-κ
   (put-E (↦))
   (put-κ κ)
   (δ oⁿ (reverse (cons bₙ b)))
   "cek5"]

  [V
   #:when (not (X? V))
   E ← get-E
   `(op (,c ... ,oⁿ) ((,M ,Eₘ) ,cₗ ...) ,κ) ← get-κ
   (put-E Eₘ)
   (put-κ `(op ((,V ,E) ,@c ,oⁿ) (,@cₗ) ,κ))
   M
   "cek6"]

  [X
   E ← get-E
   `(,V ,E′) ≔ (E X)
   (put-E E′)
   V
   "cek7"])

(define-match-expander mkCEK
  (syntax-parser
    [(_ M E κ) #'(cons (cons M E) κ)])
  (syntax-parser
    [(_ M E κ) #'(cons (cons M E) κ)]))

(define step⊢->cek (let-values ([(mrun reducer) (⊢->cek)])
                     (match-λ
                      [(mkCEK M E (? κ? κ))
                       (mrun κ E (reducer M))])))
(define ⊢->>cek (compose1 car (repeated step⊢->cek)))

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

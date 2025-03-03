#lang racket
(require lightstep/base lightstep/syntax lightstep/transformers
         (only-in "iswim.rkt" [ISWIM orig-ISWIM] FV δ))

(module+ test (require rackunit))

;;=============================================================================
;; 6.4 The CEK Machine

(define-language CEK #:super orig-ISWIM
  [κ ∷=
     'mt
     `(fn (,V ,ξ) ,(? κ? κ))
     `(ar (,M ,ξ) ,(? κ? κ))
     `(op ,(? list? VξsOⁿ) ,(? list? Mξs) ,(? κ? κ))]
  [ξ ∷= (? map?)])

(define-reduction (⊢->cek-rules)
  #:monad (StateT #f (StateT #f (NondetT ID)))
  #:do [(define get-ξ (bind get (compose1 return car)))
        (define get-κ (bind get (compose1 return cdr)))
        (define (put-ξ ξ)
          (do (cons _ κ) ← get
              (put (cons ξ κ))))
        (define (put-κ κ)
          (do (cons ξ _) ← get
              (put (cons ξ κ))))]
  [`(,M₁ ,M₂)
   ξ ← get-ξ
   κ ← get-κ
   (put-κ `(ar (,M₂ ,ξ) ,κ))
   M₁
   "cek1"]

  [`(,(? oⁿ? oⁿ) ,M ,M′ ...)
   ξ ← get-ξ
   κ ← get-κ
   (put-κ `(op (,oⁿ) ,(map (λ (m) `(,m ,ξ)) M′) ,κ))
   M
   "cek2"]

  [V
   #:when (not (X? V))
   ξ ← get-ξ
   `(fn ((λ ,X₁ ,M) ,ξ′) ,κ) ← get-κ
   (put-ξ (ξ′ X₁ `(,V ,ξ)))
   (put-κ κ)
   M
   "cek3"]

  [V
   #:when (not (X? V))
   ξ ← get-ξ
   `(ar (,M ,ξ′) ,κ) ← get-κ
   (put-ξ ξ′)
   (put-κ `(fn (,V ,ξ) ,κ))
   M
   "cek4"]

  [(? b? bₙ)
   `(op ((,(? b? b) ,_) ... ,oⁿ) () ,κ) ← get-κ
   (put-ξ (↦))
   (put-κ κ)
   (δ oⁿ (reverse (cons bₙ b)))
   "cek5"]

  [V
   #:when (not (X? V))
   ξ ← get-ξ
   `(op (,c ... ,oⁿ) ((,M ,ξₘ) ,cₗ ...) ,κ) ← get-κ
   (put-ξ ξₘ)
   (put-κ `(op ((,V ,ξ) ,@c ,oⁿ) (,@cₗ) ,κ))
   M
   "cek6"]

  [X
   ξ ← get-ξ
   `(,V ,ξ′) ≔ (ξ X)
   (put-ξ ξ′)
   V
   "cek7"])

(define ⊢->cek (call-with-values
                (λ () (invoke-unit (⊢->cek-rules)))
                (λ (mrun reducer)
                  (λ (ς) (mrun (cdr ς) (cdar ς) (reducer (caar ς)))))))
(define ⊢->>cek (compose1 car (repeated ⊢->cek)))

(define/match (evalcek m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>cek (cons (cons M (↦)) 'mt))
     [(set (cons (cons (? b? b) (? ξ? _)) 'mt))
      b]
     [(set (cons (cons `(λ ,X ,(? M? N)) (? ξ? _)) 'mt))
      'function]
     [x (error 'evalcek "invalid final state: ~a" x)])]
  [_ (error 'evalcek "invalid input: ~a" m)])

(module+ test
  (check-equal? (evalcek '(+ (* 9 (↑ 2 3)) 3)) 75)
  (check-equal? (evalcek '(((λ f (λ x (f x))) (λ y (+ y y))) 8)) 16))

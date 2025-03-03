#lang racket
(require lightstep/base lightstep/syntax lightstep/transformers
         (only-in "iswim.rkt" [ISWIM orig-ISWIM] FV subst δ))

(module+ test (require rackunit))

;;=============================================================================
;; 6.3 The CK Machine

(define-language CK #:super orig-ISWIM
  [κ ∷=
     'mt
     `(fn ,V ,κ)
     `(ar ,M ,κ)
     `(op ,(? list? VsOⁿ) ,(? list? Ns) ,κ)])

(define-reduction (⊢->ck-rules)
  #:monad (StateT #f (NondetT ID))

  [`(,M₁ ,M₂)
   κ ← get
   (put `(ar ,M₂ ,κ))
   M₁
   "ck1"]

  [`(,(? oⁿ? oⁿ) ,M ,M′ ...)
   κ ← get
   (put `(op (,oⁿ) (,@M′) ,κ))
   M
   "ck2"]

  [V
   `(fn (λ ,X ,M) ,κ) ← get
   (put κ)
   (subst M X V)
   "ck3"]

  [V
   `(ar ,M ,κ) ← get
   (put `(fn ,V ,κ))
   M
   "ck4"]

  [(? b? bₙ)
   `(op (,(? b? b) ... ,oⁿ) () ,κ) ← get
   (put κ)
   (δ oⁿ `(,@(reverse (cons bₙ b))))
   "ck5"]

  [V
   `(op (,V′ ... ,oⁿ) (,M ,M′ ...) ,κ) ← get
   (put `(op (,V ,@V′ ,oⁿ) (,@M′) ,κ))
   M
   "ck6"])

(define ⊢->ck (call-with-values
               (λ () (invoke-unit (⊢->ck-rules)))
               (λ (mrun reducer)
                 (λ (ς) (mrun (cdr ς) (reducer (car ς)))))))
(define ⊢->>ck (compose1 car (repeated ⊢->ck)))

(define/match (evalck m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>ck (cons M 'mt))
     [(set (cons (? b? b) 'mt))
      b]
     [(set (cons `(λ ,X ,(? M? N)) 'mt))
      'function]
     [x (error 'evalck "invalid final state: ~a" x)])]
  [_ (error 'evalck "invalid input: ~a" m)])

(module+ test
  (check-equal? (⊢->>ck (cons '(((λ x x) (λ y y)) 1) 'mt))
                (set (cons 1 'mt)))
  (check-equal? (⊢->>ck (cons '(+ (add1 2) (* 3 4)) 'mt))
                (set (cons 15 'mt)))

  (check-equal? (evalck '(+ (* 9 (↑ 2 3)) 3)) 75)
  (check-equal? (evalck '(((λ f (λ x (f x))) (λ y (+ y y))) 8)) 16))

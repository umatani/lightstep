#lang racket/base
(require lightstep/base lightstep/syntax lightstep/transformers
         (only-in racket/unit invoke-unit)
         (only-in "iswim.rkt" [ISWIM orig-ISWIM] FV subst δ)
         (only-in "cc.rkt" ECxt □))

(module+ test (require rackunit))

(define-language ISWIM #:super orig-ISWIM)

;;=============================================================================
;; 6.2 The CC Machine

(define-reduction (⊢->scc-rules)
  #:monad (StateT #f (NondetT ID))

  [`(,M₁ ,M₂)
   (ECxt (□)) ← get
   (put (ECxt `(,(□) ,M₂)))
   M₁
   "scc1"]

  [`(,(? oⁿ? oⁿ) ,M₁ ,M ...)
   (ECxt (□)) ← get
   (put (ECxt `(,oⁿ ,(□) ,@M)))
   M₁
   "scc2"]

  [V
   (ECxt `((λ ,X ,M) ,(□))) ← get
   (put (ECxt (□)))
   (subst M X V)
   "scc3"]

  [V
   (ECxt `(,(□) ,M)) ← get
   (put (ECxt `(,V ,(□))))
   M
   "scc4"]

  [(? b? bₙ)
   (ECxt `(,(? oⁿ? oⁿ) ,(? b? b) ... ,(□))) ← get
   (put (ECxt (□)))
   (δ oⁿ `(,@b ,bₙ))
   "scc5"]

  [V
   (ECxt `(,(? oⁿ? oⁿ) ,V₁ ... ,(□) ,M₁ ,M ...)) ← get
   (put (ECxt `(,oⁿ ,@V₁ ,V ,(□) ,@M)))
   M₁
   "scc6"])

(define ⊢->scc (call-with-values
                (λ () (invoke-unit (⊢->scc-rules)))
                (λ (mrun reducer)
                  (λ (ς) (mrun (cdr ς) (reducer (car ς)))))))
(define ⊢->>scc (compose1 car (repeated ⊢->scc)))

(define/match (evalscc m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>scc (cons M (□)))
     [(set (cons (? b? b) (□)))
      b]
     [(set (cons `(λ ,X ,(? M? N)) (□)))
      'function]
     [x (error 'evalscc "invalid final state: ~a" x)])]
  [_ (error 'evalscc "invalid input: ~a" m)])

(module+ test
  (check-equal? (⊢->>scc (cons '(((λ x x) (λ y y)) 1) (□)))
                (set (cons 1 (□))))
  (check-equal? (⊢->>scc (cons '(+ (add1 2) (* 3 4)) (□)))
                (set (cons 15 (□))))

  (check-equal? (evalscc '(+ (* 9 (↑ 2 3)) 3)) 75)
  (check-equal? (evalscc '(((λ f (λ x (f x))) (λ y (+ y y))) 8)) 16))

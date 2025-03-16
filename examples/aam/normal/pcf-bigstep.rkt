#lang racket/base
(require lightstep/base lightstep/syntax lightstep/inference
         (only-in lightstep/monad mapM)
         (only-in "pcf.rkt" PCF δ))
(provide PCF⇓)

(module+ test (require rackunit))

;;-----------------------------------------------------------------------------
;; 3.4 Evaluation

(define-language PCF⇓ #:super PCF
  [V ∷= N O
        `(,L ,(? ρ?))
        `((μ [,X : ,T] ,L) ,(? ρ?))]
  [ρ ∷= (? map? X→V)])

;; M ρ ⇓ V
(define-inference (⇓-rules)
  #:do [(define (ext Γ xs vs)
          (foldr (λ (x v Γ) (Γ x v)) Γ xs vs))]
  #:forms ([`(,M:i ,ρ:i ⇓ ,V:o) #:where V ← (⇓-rules `(,M ,ρ))])

  [------------------
   `(,N ,(? ρ?) ⇓ ,N)]

  [------------------
   `(,O ,(? ρ?) ⇓ ,O)]

  [-------------------------
   `(,L ,(? ρ? ρ) ⇓ (,L ,ρ))]

  [-----------------------------------------------------
   `((μ [,X : ,T] ,L) ,(? ρ? ρ) ⇓ ((μ [,X : ,T] ,L) ,ρ))]

  [V ≔ (ρ X)
   --------------------
   `(,X ,(? ρ? ρ) ⇓ ,V)]

  [`(,M₀ ,ρ ⇓ ,N)
   M ≔ (if (zero? N) M₁ M₂)
   `(,M ,ρ ⇓ ,V)
   -----------------------------------
   `((if0 ,M₀ ,M₁ ,M₂) ,(? ρ? ρ) ⇓ ,V)]

  [`(,M₀ ,ρ ⇓ ,O)
   `(,N₁ ...) ← (mapM (λ (m) (⇓-rules `(,m ,ρ))) M₁)
   N ≔ (δ `(,O ,@N₁))
   -------------------------------------------------
   `((,M₀ ,M₁ ...) ,(? ρ? ρ) ⇓ ,N)]

  [`(,M₀ ,ρ ⇓ ((λ ([,X₁ : ,T] ...) ,M) ,ρ₁))
   `(,V₁ ...) ← (mapM (λ (m) (⇓-rules `(,m ,ρ))) M₁)
   `(,M ,(ext ρ₁ X₁ V₁) ⇓ ,V)
   -------------------------------------------------
   `((,M₀ ,M₁ ...) ,(? ρ? ρ) ⇓ ,V)]

  [`(,M₀ ,ρ ⇓ ,(and f `((μ [,Xₐ : ,Tₐ] (λ ([,X₁ : ,T] ...) ,M)) ,ρ₁)))
   `(,V₁ ...) ← (mapM (λ (m) (⇓-rules `(,m ,ρ))) M₁)
   `(,M ,(ext ρ₁ (cons Xₐ X₁) (cons f V₁)) ⇓ ,V)
   -------------------------------------------------------------------
   `((,M₀ ,M₁ ...) ,(? ρ? ρ) ⇓ ,V)                                    ])

;; M ρ → V
(define (⇓ M ρ) (letrec-values ([(mrun reducer) (⇓-rules)])
                      (mrun (reducer `(,M ,ρ)))))

;; M ρ V → Boolean
(define (⇓? M ρ v) (∈ v (⇓ M ρ)))

(module+ test
  (require (only-in (submod "pcf.rkt" test) fact-5))

  (check-equal? (⇓ fact-5 (↦)) (set 120))
  (check-true (⇓? fact-5 (↦) 120)))

#lang racket/base
(require lightstep/base lightstep/syntax
         (only-in lightstep/monad mapM)
         (only-in "common.rkt" mmap-ext mmap-lookup)
         (only-in "pcf.rkt" PCF δ))
(provide PCF⇓)

(module+ test (require rackunit))

;; TODO: monadic version

;;-----------------------------------------------------------------------------
;; 3.4 Evaluation

(define-language PCF⇓ #:super PCF
  [V ∷=
     N O
     `(,L ,(? ρ?))
     `((μ [,X : ,T] ,L) ,(? ρ?))]
  [ρ ∷= (? map?)])

(define-reduction (⇓)
  [`(,N ,(? ρ?))
   ; -->
   N]

  [`(,O ,(? ρ?))
   ; -->
   O]

  [`(,L ,(? ρ? ρ))
   ; -->
   `(,L ,ρ)]

  [`((μ [,X : ,T] ,L) ,(? ρ? ρ))
   ; -->
   `((μ [,X : ,T] ,L) ,ρ)]

  [`(,X ,(? ρ? ρ))
   ; where
   V ← (for/monad+ ([V (in-set (mmap-lookup ρ X))])
         (return V))
   ; -->
   V]

  [`((if0 ,M₀ ,M₁ ,M₂) ,(? ρ? ρ))
   ; where
   N ← (⇓ `(,M₀ ,ρ))
   M ≔ (if (zero? N) M₁ M₂)
   V ← (⇓ `(,M ,ρ))
   ; -->
   V]

  [`((,M₀ ,M₁ ...) ,(? ρ? ρ))
   ; where
   O ← (⇓ `(,M₀ ,ρ))
   `(,N₁ ...) ← (mapM (λ (m) (⇓ `(,m ,ρ))) M₁)
   N ≔ (δ `(,O ,@N₁))
   ; -->
   N]

  [`((,M₀ ,M₁ ...) ,(? ρ? ρ))
   ; where
   `((λ ([,X₁ : ,T] ...) ,M) ,(? ρ? ρ₁)) ← (⇓ `(,M₀ ,ρ))
   `(,V₁ ...) ← (mapM (λ (m) (⇓ `(,m ,ρ))) M₁)
   V ← (⇓ `(,M ,(apply mmap-ext ρ₁ (map list X₁ V₁))))
   ; -->
   V]

  [`((,M₀ ,M₁ ...) ,(? ρ? ρ))
   ; where
   (and f `((μ [,X : ,T₁] (λ ([,X₁ : ,T₂] ...) ,M))
            ,(? ρ? ρ₁))) ← (⇓ `(,M₀ ,ρ))
   `(,V₁ ...) ← (mapM (λ (m) (⇓ `(,m ,ρ))) M₁)
   V ← (⇓ `(,M ,(apply mmap-ext ρ₁ `[,X ,f] (map list X₁ V₁))))
   ; -->
   V])

(define (run-⇓ M ρ) (letrec-values ([(mrun reducer) (⇓)])
                      (mrun (reducer `(,M ,ρ)))))

(define (⇓? M ρ v) (∈ v (run-⇓ M ρ)))

(module+ test
  (require (only-in (submod "pcf.rkt" test) fact-5))
  (check-equal? (run-⇓ fact-5 (↦)) (set 120))
  (check-true (⇓? fact-5 (↦) 120)))

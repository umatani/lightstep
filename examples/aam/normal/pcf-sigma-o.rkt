#lang racket/base
(require lightstep/base lightstep/syntax lightstep/inference
         (only-in "pcf.rkt" δ)
         (only-in "pcf-rho.rkt" vρ-rules)
         (only-in "pcf-varsigma.rkt" -->vς-rules)
         (only-in "pcf-sigma.rkt" injσ)
         (only-in "pcf-sigma-star.rkt" [PCFσ* orig-PCFσ*] alloc*)
         (only-in "pcf-sigma-star-sigma.rkt" -->vσ*/Σ-rules))
(provide lookup-Σ-rules ext-Σ)

(module+ test (require rackunit))

;;-----------------------------------------------------------------------------
;; 4.2 Set-based heap

(define-language PCFσ* #:super orig-PCFσ*)

;; (Σ A) --> U
(define-inference (lookup-Σ-rules)
  [U  ← (m+ (Σ A))
   ---------------
   `((,Σ ,A) → ,U)])

;; (α ↦ β) List(α) List(β) → (α ↦ β)
(define (ext-Σ m ks vs)
  (foldr (λ (k v m) (pmap-add1 m k v)) m ks vs))

;; δ --> δ
(define-inference (-->vσ∘/Σ-rules alloc ext-Σ lookup-Σ)
  #:super [(-->vσ*/Σ-rules alloc ext-Σ lookup-Σ)])

;; σ → 𝒫(σ)
(define -->vσ∘ (call-with-values
                (λ ()
                  (-->vσ∘/Σ-rules alloc* ext-Σ (reducer-of (lookup-Σ-rules))))
                compose1))
(define -->>vσ∘ (compose1 car (repeated -->vσ∘)))

(module+ test
  (require (only-in (submod "pcf.rkt" test) fact-5))

  (check-equal? (-->>vσ∘ (injσ '((λ ([f : (num → num)])
                                   ((λ ([_ : num]) (f 0)) (f 1)))
                                 (λ ([z : num]) z)))) (set 0))

  (check-equal? (-->>vσ∘ (injσ fact-5)) (set 120)))

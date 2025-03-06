#lang racket/base
(require lightstep/base lightstep/syntax
         (only-in "common.rkt" mmap-ext mmap-lookup)
         (only-in "pcf.rkt" δ)
         (only-in "pcf-rho.rkt" vρ-rules)
         (only-in "pcf-varsigma.rkt" -->vς-rules)
         (only-in "pcf-sigma.rkt" PCFσ injσ formals alloc)
         (only-in "pcf-sigma-alloc.rkt"-->vσ/alloc-rules))
(module+ test (require rackunit))

;; Abstracting Abstract Machines from:
;;   https://dvanhorn.github.io/redex-aam-tutorial/

;; TODO: monadic version

;;-----------------------------------------------------------------------------
;; 3.10 Heap-allocated continuations

(define-language PCFσ* #:super PCFσ
  [K ∷= '() `(,F ,A)]
  [U ∷= V K])

(define/match (alloc* σ) #:super alloc
  [`(((if0 ,S₀ ,C₁ ,C₂) ,K) ,Σ)
   `(((if0 □ ,C₁ ,C₂) ,(gensym 'if0)))]
  [`(((,V ... ,S ,C ...) ,K) ,Σ)
   `(((,@V □ ,@C) ,(gensym 'app)))])

(module+ test
  ;; (alloc* `(((if0 ((add1 2) ,(↦)) (3 ,(↦)) (4 ,(↦))) ()) ,(↦)))
  ;; (alloc* `(((((λ ([y : num]) y) ,(↦)) ((add1 2) ,(↦))) ()) ,(↦)))
  ;; (alloc* `(((((λ ([y : num] [z : num]) y) ,(↦)) 5 7) ()) ,(↦)))
  )

(define-reduction (-->vσ*/alloc-rules alloc*)
  #:super [(-->vσ/alloc-rules alloc*)]

  ; Eval
  [(and σ `(((if0 ,S₀ ,C₁ ,C₂) ,K) ,Σ))
   ; where
   `(,A) ≔ (alloc* σ)
   ; -->
   `((,S₀ ((if0 □ ,C₁ ,C₂) ,A)) ,(mmap-ext Σ `[,A ,K]))
   "ev-if"]

  [(and σ `(((,V ... ,S ,C ...) ,K) ,Σ))
   ; where
   `(,A) ≔ (alloc* σ)
   ; -->
   `((,S ((,@V □ ,@C) ,A)) ,(mmap-ext Σ `[,A ,K]))
   "ev-app"]

  ; Continue
  [`((,V ((if0 □ ,C₁ ,C₂) ,A)) ,Σ)
   ; where
   K ← (mmap-lookup Σ A)
   ; -->
   `(((if0 ,V ,C₁ ,C₂) ,K) ,Σ)
   "co-if"]

  [`((,V ((,V₀ ... □ ,C₀ ...) ,A)) ,Σ)
   ; where
   K ← (mmap-lookup Σ A)
   ; -->
   `(((,@V₀ ,V ,@C₀) ,K) ,Σ)
   "co-app"])

(define -->vσ* (call-with-values
                (λ () (-->vσ*/alloc-rules alloc*))
                compose1))

(module+ test
  (require (only-in (submod "pcf.rkt" test) fact-5))
  (check-equal? (car ((repeated -->vσ*) (injσ fact-5))) (set 120)))

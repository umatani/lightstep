#lang racket/base
(require lightstep/base lightstep/syntax
         (only-in "common.rkt" mmap-ext mmap-lookup)
         (only-in "pcf.rkt" δ)
         (only-in "pcf-rho.rkt" PCFρ vρ injρ))
(provide PCFς -->vς injς)

(module+ test (require rackunit))

;; Abstracting Abstract Machines from:
;;   https://dvanhorn.github.io/redex-aam-tutorial/

;; TODO: monadic version

;;-----------------------------------------------------------------------------
;; 3.7 Eval/Continue/Apply machine

(define-language PCFς #:super PCFρ
  [F ∷=
     `(,V ... □ ,C ...)
     `(if0 □ ,C₁ ,C₂)]
  [K ∷= `[,F ...]]
  [S ∷= ; serious terms S ∩ V = ∅, C = S ∪ V
     `(,N ,(? ρ?))
     `(,O ,(? ρ?))
     `(,X ,(? ρ?))
     `((,M ,M′ ...) ,(? ρ?))
     `((if0 ,M₀ ,M₁ ,M₂) ,(? ρ?))
     `(if0 ,C₀ ,C₁ ,C₂)
     `(,C ,C′ ...)]
  [ς ∷= `(,C ,K) V])

(define-reduction (-->vς)
  #:do [(define-reduction (rules) #:super [(vρ)])
        (define →vρ (reducer-of (rules)))]
  ; Apply
  [`(,C ,K)
   ; where
   C′ ← (→vρ C)
   ; -->
   `(,C′ ,K)
   "ap"]

  ; Eval
  [`((if0 ,S₀ ,C₁ ,C₂) [,F ...])
   ; -->
   `(,S₀ [(if0 □ ,C₁ ,C₂) ,@F])
   "ev-if"]

  [`((,V ... ,S ,C ...) [,F ...])
   ; -->
   `(,S [(,@V □ ,@C) ,@F])
   "ev-app"]

  ; Continue
  [`(,V [])
   ; -->
   V
   "halt"]

  [`(,V [(if0 □ ,C₁ ,C₂) ,F ...])
   ; -->
   `((if0 ,V ,C₁ ,C₂) [,@F])
   "co-if"]

  [`(,V [(,V₀ ... □ ,C₀ ...) ,F ...])
   ; -->
   `((,@V₀ ,V ,@C₀) [,@F])
   "co-app"])

(define step-->vς (call-with-values (λ () (-->vς)) compose1))

(define (injς M)
  `(,(injρ M) []))

(module+ test
  (require (only-in (submod "pcf.rkt" test) fact-5))
  (check-equal? (car ((repeated step-->vς) (injς fact-5)))
                (set 120))
  (check-equal? (car ((repeated step-->vς)
                      (injς '((λ ([x : num]) x) (add1 5)))))
                (set 6)))

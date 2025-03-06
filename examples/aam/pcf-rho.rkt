#lang racket/base
(require (for-syntax racket/base
                     (only-in syntax/parse syntax-parser id))
         lightstep/base lightstep/syntax
         (only-in racket/match define-match-expander)
         (only-in "common.rkt" mmap-ext mmap-lookup)
         (only-in "pcf.rkt" δ)
         (only-in "pcf-bigstep.rkt" PCF⇓))
(provide PCFρ vρ injρ)

(module+ test (require rackunit))

;; Abstracting Abstract Machines from:
;;   https://dvanhorn.github.io/redex-aam-tutorial/

;; TODO: monadic version

;;-----------------------------------------------------------------------------
;; 3.6 Explicit substitutions

(define-language PCFρ #:super PCF⇓
  [C ∷=
     V
     `(,M ,(? ρ?))
     `(if0 ,C₀ ,C₁ ,C₂)
     `(,C₀ ,C₁ ...)]

  [redex ∷=
         `((if0 ,M ...) ,(? ρ?))
         `((,M ...) ,(? ρ?))
         `(,O ,(? ρ?))
         `(,N ,(? ρ?))
         `(,X ,(? ρ?))
         `(((λ ([,X : ,T] ...) ,M) ,(? ρ?)) ,V ...)
         `(((μ [,X′ : ,T′] (λ ([,X : ,T] ...) ,M)) ,(? ρ?)) ,V ...)
         `(,O ,V ...)
         `(if0 ,N ,C₁ ,C₂)])

(define-match-expander ECxt
  (syntax-parser
    [(ECxt □:id)
     #'(... (cxt ECxt [□ (and □ (? redex?))]
                 `(,V ... ,(? C? □) ,C ...)
                 `(if0 ,(? C? □) ,C₁ ,C₂)))]))

(define-reduction (vρ)
  [`((if0 ,M ...) ,(? ρ? ρ))
   ; -->
   `(if0 ,@(map (λ (m) `(,m ,ρ)) M))
   "ρ-if"]

  [`((,M ...) ,(? ρ? ρ))
   ; -->
   `(,@(map (λ (m) `(,m ,ρ)) M))
   "ρ-app"]

  [`(,O ,(? ρ? ρ))
   ; -->
   O
   "ρ-op"]

  [`(,N ,(? ρ? ρ))
   ; -->
   N
   "ρ-num"]

  [`(,X ,(? ρ? ρ))
   ; where
   V ← (for/monad+ ([v (mmap-lookup ρ X)]) (return v))
   ; -->
   V
   "ρ-x"]

  [`(((λ ([,X : ,T] ...) ,M) ,(? ρ? ρ)) ,V ...)
   ; -->
   `(,M ,(apply mmap-ext ρ (map list X V) ))
   "β"]

  [`(,(and f `((μ [,X′ : ,T′] (λ ([,X : ,T] ...) ,M)) ,(? ρ? ρ))) ,V ...)
   ; -->
   `(,M ,(apply mmap-ext ρ `[,X′ ,f] (map list X V)))
   "rec-β"]

  [`(,O ,V ...)
   ; where
   V₁ ≔ (δ `(,O ,@V))
   ; -->
   V₁
   "δ"]

  [`(if0 0 ,C₁ ,C₂)
   ; -->
   C₁
   "if-t"]

  [`(if0 ,N ,C₁ ,C₂)
   #:when (not (equal? 0 N))
   ; -->
   C₂
   "if-f"])

(define-reduction (-->vρ)
  #:do [(define →vρ (reducer-of (vρ)))]
  [(ECxt c)
   ; where
   C′ ← (→vρ c)
   ; -->
   (ECxt C′)
   "EC"])

(define step-->vρ (call-with-values (λ () (-->vρ)) compose1))

(define (injρ M)
  `(,M ,(↦)))

(module+ test
  (require (only-in (submod "pcf.rkt" test) fact-5))
  (check-equal? (car ((repeated step-->vρ) (injρ fact-5))) (set 120)))

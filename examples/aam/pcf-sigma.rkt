#lang racket/base
(require lightstep/base lightstep/syntax
         (only-in "common.rkt" mmap-ext mmap-lookup)
         (only-in "pcf.rkt" δ)
         (only-in "pcf-rho.rkt" vρ-rules)
         (only-in "pcf-varsigma.rkt" PCFς -->vς-rules injς))
(provide PCFσ -->vσ-rules injσ formals alloc)

(module+ test (require rackunit))

;; Abstracting Abstract Machines from:
;;   https://dvanhorn.github.io/redex-aam-tutorial/

;; TODO: monadic version

;;-----------------------------------------------------------------------------
;; 3.8 Heap-allocated bindings

(define-language PCFσ #:super PCFς
  [Σ ∷= (? map?)]
  [A ∷= (? (λ (_) #t))]
  [σ ∷= `(,(? ς?) ,Σ) V])

(define-reduction (-->vσ-rules)
  #:do [(define-reduction (-->vς′-rules) #:super [(-->vς-rules)]
          #:do [;; remove rules manually
                (define-reduction (vρ′-rules) #:super [(vρ-rules)]
                  [x #:when #f x "ρ-x"]
                  [x #:when #f x "β"]
                  [x #:when #f x "rec-β"])
                (define vρ′ (reducer-of (vρ′-rules)))]
          ; Apply
          [`(,C ,K)
           ; where
           C′ ← (vρ′ C)
           ; -->
           `(,C′ ,K)
           "ap"])
        (define -->vς′ (reducer-of (-->vς′-rules)))]
  [`(,(? ς? ς) ,Σ)
   ; where
   (? ς? ς′) ← (-->vς′ ς)
   ; -->
   `(,ς′ ,Σ)]

  [`(,N ,Σ)
   ; -->
   N
   "discard-Σ-N"]

  [`(,O ,Σ)
   ; -->
   O
   "discard-Σ-O"]

  [`(((,X ,(? ρ? ρ)) ,K) ,Σ)
   ; where
   A ← (mmap-lookup ρ X)
   V ← (mmap-lookup Σ A)
   ; -->
   `((,V ,K) ,Σ)
   "ρ-x"]

  [(and σ `(((((λ ([,X : ,T] ...) ,M) ,(? ρ? ρ)) ,V ...) ,K) ,Σ))
   ; where
   `(,A ...) ≔ (alloc σ)
   ; -->
   `(((,M ,(apply mmap-ext ρ (map list X A))) ,K)
     ,(apply mmap-ext Σ (map list A V)))
   "β"]

  [(and σ `(((,(and f `((μ [,X′ : ,T′]
                           (λ ([,X : ,T] ...) ,M)) ,(? ρ? ρ))) ,V ...)
             ,K) ,Σ))
   ; where
   `(,A′ ,A ...) ≔ (alloc σ)
   ; -->
   `(((,M ,(apply mmap-ext ρ `[,X′ ,A′] (map list X A))) ,K)
     ,(apply mmap-ext Σ `[,A′ ,f] (map list A V)))
   "rec-β"])

(define -->vσ (call-with-values
               (λ () (-->vσ-rules))
               compose1))

(define (injσ M)
  `(,(injς M) ,(↦)))

(define (formals M)
  (match M
    [`(λ ([,X : ,T] ...) ,M)
     `(,@X)]
    [`(μ [,X′ : ,T′] ,L)
     (match-let ([`(,X ...) (formals L)])
       `(,X′ ,@X))]))

(define/match (alloc σ)
  [`((((,M ,(? ρ?)) ,V ...) ,K) ,Σ)
   (map (λ (x) (list x (gensym x))) (formals M))])

(module+ test
  (require (only-in (submod "pcf.rkt" test) fact-5))

  ;(alloc `(((((λ ([y : num] [z : num]) y) ,(↦)) 5 7) []) ,(↦)))
  ;(-->vσ `(((((λ ([y : num] [z : num]) y) ,(↦)) 5 7) []) ,(↦)))

  (check-equal?  (car ((repeated -->vσ) (injσ fact-5))) (set 120)))

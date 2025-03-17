#lang racket/base
(require lightstep/base)

(module+ test (require rackunit))

;;=============================================================================
;; Syntax

;; B --> #t
(define-reduction (∈B)
  ['t
   #t]
  ['f
   #t]
  [`(● ,b₀ ,b₁)
   #t ← (∈B b₀)
   #t ← (∈B b₁)
   #t])

;; B → 𝒫(#t)
(define run-∈B (call-with-values (λ () (∈B)) compose1))

;; B → Boolean
(define (B? B)
  (match (run-∈B B)
    [(set #t) #t]
    [(set)    #f]
    [_ (error "no such case")]))

(module+ test
  (check-true (B? '(● t (● f t))))
  (check-true (B? 't))
  (check-false (B? '●))
  (check-true (B? '(● (● f t) (● f f))))
  (check-false (B? '(● (f) (t))))
  (check-false (B? "hello")))

;;=============================================================================
;; Semantics

;; B --> B
(define-reduction (r)
  [`(● f ,B₁)
   B₁
   "a"]
  [`(● t ,B₁)
   't
   "b"])

;; B --> B
(define-reduction (≍r-v0) #:super [(r)]
  [B₁
   B₁
   "c"])

;; B --> B
(define-reduction (≍r r)
  [B₁
   B₂ ← (r B₁)
   B₂
   "ab"]
  [B₁
   B₁
   "c"])

;; B → 𝒫(B)
(define step-r (call-with-values (λ () (r)) compose1))
(define ->>r (repeated step-r))

(module+ test
  (check-equal? (car (->>r '(● f (● f (● t f))))) (set 't))
  (check-equal? (car (->>r '(● f (● f (● f f))))) (set 'f)))

;; B --> B
(define-reduction (-->r) #:super [(r)]
  [`(● ,B₁ ,B₂)
   B₁′ ← (-->r B₁)
   `(● ,B₁′ ,B₂)]

  [`(● ,B₁ ,B₂)
   B₂′ ← (-->r B₂)
   `(● ,B₁ ,B₂′)])

;; B → 𝒫(B)
(define step-->r (call-with-values (λ () (-->r)) compose1))
(define -->>r (repeated step-->r))

(module+ test
  (check-equal? (step-->r '(● (● f t) f)) (set '(● t f)))
  (check-equal? (step-->r '(● t f)) (set 't))
  (check-equal? (car (-->>r '(● (● f t) f))) (set 't))
  (check-equal? (car (-->>r '(● f (● (● t f) f)))) (set 't)))

;; B --> #t
(define-reduction (∈R)
  ['t
   #t]
  ['f
   #t])

;; B → 𝒫(#t)
(define run-∈R (call-with-values (λ () (∈R)) compose1))

;; B → Boolean
(define (R? B)
  (match (run-∈R B)
    [(set #t) #t]
    [(set)    #f]
    [_ (error "no such case")]))

(module+ test
  (check-false (R? '(● t (● f t))))
  (check-true (R? 't))
  (check-true (R? 'f))
  (check-false (R? '●))
  (check-false (R? '(● (● f t) (● f f))))
  (check-false (R? '(● (f) (t))))
  (check-false (R? "hello")))

;; (B → 𝒫(B)) B → B
(define ((evalᵣ -->) B)
  (match (--> B)
    [(set R) R]
    [(set _) (error "get stuck")]
    [_ (error "non-deterministic relation")]))

;; B → B
(define eval (evalᵣ (compose1 car -->>r)))

(module+ test
  (check-equal? (eval '(● (● f t) f)) 't)
  (check-equal? (eval '(● t f)) 't)
  (check-equal? (eval '(● (● f t) f)) 't)
  (check-equal? (eval '(● f (● (● t f) f))) 't))

#lang racket
(require lightstep/base)

(module+ test (require rackunit))

;;=============================================================================
;; Syntax

(define-reduction (∈B-rules ∈B)
  ['t
   #t]
  ['f
   #t]
  [`(● ,b₀ ,b₁)
   #t ← (∈B b₀)
   #t ← (∈B b₁)
   #t])

(define-values (mrun-∈B reducer-∈B) (invoke-unit (∈B-rules reducer-∈B)))
(define ∈B (compose1 mrun-∈B reducer-∈B))

(define (B? B)
  (match (∈B B)
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

(define-reduction (r-rules)
  [`(● f ,B₁)
   B₁
   "a"]
  [`(● t ,B₁)
   't
   "b"])

(define-reduction (≍r-rules-v0) #:super (r-rules)
  [B₁
   B₁
   "c"])

(define-reduction (≍r-rules r)
  [B₁
   B₂ ← (r B₁)
   B₂
   "ab"]
  [B₁
   B₁
   "c"])

(define-values (mrun-r reducer-r) (invoke-unit (r-rules)))
(define r (compose1 mrun-r reducer-r))
(define ->>r (repeated r))

(module+ test
  (check-equal? (car (->>r '(● f (● f (● t f))))) (set 't))
  (check-equal? (car (->>r '(● f (● f (● f f))))) (set 'f)))

(define-reduction (-->r-rules -->r) #:super (r-rules)
  [`(● ,B₁ ,B₂)
   B₁′ ← (-->r B₁)
   `(● ,B₁′ ,B₂)]

  [`(● ,B₁ ,B₂)
   B₂′ ← (-->r B₂)
   `(● ,B₁ ,B₂′)])

(define-values (mrun-->r reducer-->r) (invoke-unit (-->r-rules reducer-->r)))
(define -->r (compose1 mrun-->r reducer-->r))
(define -->>r (repeated -->r))

(module+ test
  (check-equal? (-->r '(● (● f t) f)) (set '(● t f)))
  (check-equal? (-->r '(● t f)) (set 't))
  (check-equal? (car (-->>r '(● (● f t) f))) (set 't))
  (check-equal? (car (-->>r '(● f (● (● t f) f)))) (set 't)))


(define-reduction (∈R-rules ∈R)
  ['t
   #t]
  ['f
   #t])

(define-values (mrun-∈R reducer-∈R) (invoke-unit (∈R-rules reducer-∈R)))
(define ∈R (compose1 mrun-∈R reducer-∈R))

(define (R? B)
  (match (∈R B)
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

(define ((eval-r -->) B)
  (match (--> B)
    [(set R) R]
    [(set _) (error "get stuck")]
    [_ (error "non-deterministic relation")]))

(define eval (eval-r (compose1 car -->>r)))

(module+ test
  (check-equal? (eval '(● (● f t) f)) 't)
  (check-equal? (eval '(● t f)) 't)
  (check-equal? (eval '(● (● f t) f)) 't)
  (check-equal? (eval '(● f (● (● t f) f))) 't))

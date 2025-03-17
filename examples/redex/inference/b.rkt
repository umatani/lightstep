#lang racket/base
(require lightstep/base lightstep/inference)

(module+ test (require rackunit))

;;=============================================================================
;; Syntax

;; B --> #t
(define-inference (∈B-rules)
  #:forms ([`(,i:i ∈ B) #:where #t ← (∈B-rules i)])

  [--------
   '(t ∈ B)]

  [--------
   '(f ∈ B)]

  [`(,b₀ ∈ B) `(,b₁ ∈ B)
   ---------------------
   `((● ,b₀ ,b₁) ∈ B)   ])

;; B → 𝒫(#t)
(define ∈B (call-with-values (λ () (∈B-rules)) compose1))

;; B → Boolean
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

;; B --> B
(define-inference (r-rules)
  [------------------ "a"
   `((● f ,B₁) → ,B₁)    ]

  [---------------- "b"
   `((● t ,B₁) → t)    ])

;; B --> B
(define-inference (≍r-v0-rules) #:super [(r-rules)]
  [------------ "c"
   `(,B₁ → ,B₁)    ])

;; B --> B
(define-inference (≍r-rules r)
  #:do [(define rr (reducer-of (r-rules)))]
  #:forms (.... [`(,i →′ ,o) #:where o ← (rr i)])

  [`(,B₁ →′ ,B₂)
   ------------- "ab"
   `(,B₁ → ,B₂)      ]

  [------------ "c"
   `(,B₁ → ,B₁)    ])

;; B → 𝒫(B)
(define ->>r (compose1 car (repeated (call-with-values
                                      (λ () (r-rules)) compose1))))

(module+ test
  (check-equal? (->>r '(● f (● f (● t f)))) (set 't))
  (check-equal? (->>r '(● f (● f (● f f)))) (set 'f)))

;; B --> B
(define-inference (-->r-rules) #:super [(r-rules)]
  [`(,B₁ → ,B₁′)
   -----------------------------
   `((● ,B₁ ,B₂) → (● ,B₁′ ,B₂))]

  [`(,B₂ → ,B₂′)
   -----------------------------
   `((● ,B₁ ,B₂) → (● ,B₁ ,B₂′))])

;; B → 𝒫(B)
(define -->r (call-with-values (λ () (-->r-rules)) compose1))
(define -->>r (compose1 car (repeated -->r)))

(module+ test
  (check-equal? (-->r '(● (● f t) f)) (set '(● t f)))
  (check-equal? (-->r '(● t f)) (set 't))
  (check-equal? (-->>r '(● (● f t) f)) (set 't))
  (check-equal? (-->>r '(● f (● (● t f) f))) (set 't)))

;; B --> #t
(define-inference (∈R-rules)
  #:forms ([`(,i:i ∈ R) #:where #t ← (∈R-rules i)])

  [--------
   '(t ∈ R)]

  [--------
   '(f ∈ R)])

;; B → 𝒫(#t)
(define ∈R (call-with-values (λ () (∈R-rules)) compose1))

;; B → Boolean
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

;; (B → 𝒫(B)) B → B
(define ((evalᵣ -->) B)
  (match (--> B)
    [(set R) R]
    [(set _) (error "get stuck")]
    [_ (error "non-deterministic relation")]))

;; B → B
(define eval (evalᵣ -->>r))

(module+ test
  (check-equal? (eval '(● (● f t) f)) 't)
  (check-equal? (eval '(● t f)) 't)
  (check-equal? (eval '(● (● f t) f)) 't)
  (check-equal? (eval '(● f (● (● t f) f))) 't))

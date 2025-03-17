#lang racket/base
(require lightstep/base lightstep/syntax lightstep/inference
         (only-in "iswim.rkt" βv-rules subst)
         (only-in "e-iswim.rkt"
                  [E-ISWIM orig-E-ISWIM] ECxt FV δ δ-rules δerr-rules))

(module+ test (require rackunit))

;;=============================================================================
;; 8.1 Standard Reduction for Error ISWIM 

(define-language E-ISWIM #:super orig-E-ISWIM
  [Mre ∷= `(,V ,V) `(,(? oⁿ?) ,V ...) `(err ,(? b?))])

;; M --> M
(define-inference (ẽ-rules) #:super [(βv-rules) (δ-rules δ) (δerr-rules δ)])

;; M --> M
(define-inference (⊢->e-rules)
  #:do [(define rẽ (reducer-of (ẽ-rules)))]
  #:forms (.... [`(,i →ẽ ,o) #:where o ← (rẽ i)])

  [`(,M →ẽ ,M′)
   -------------------------
   `(,(ECxt M) → ,(ECxt M′))]

  [#:when (not (equal? x e))
   `(err ,(? b? b)) ≔ e
   -------------------------------
   `(,(and x (ECxt e)) → (err ,b))])

;; M → 𝒫(M)
(define ⊢->e (call-with-values (λ () (⊢->e-rules)) compose1))
(define ⊢->>e (compose1 car (repeated ⊢->e)))

;; M → (V ∪ ⊥)
(define/match (evalₑˢ m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>e M)
    [(set (? b? b)) b]
    [(set `(λ ,X ,M)) 'function]
    [(set `(err ,(? b? b))) `(err ,b)]
    [x (error 'evalₑˢ "invalid answer: ~s" x)])]
  [_ (error 'evalₑˢ "invalid input: ~s" m)])

(module+ test
  (check-exn #rx"invalid input" (λ () (evalₑˢ '(+ 1 x))))
  (check-equal? (evalₑˢ '(+ ((λ x x) 8) 2)) 10)
  (check-equal? (evalₑˢ '((λ x x) (λ x x))) 'function)
  
  (check-equal? (evalₑˢ '(add1 (λ x x))) '(err 0))
  (check-equal? (evalₑˢ '(/ 3 0)) '(err 0))

  (check-equal? (⊢->e '(+ (- 4 (err 1)) (err 2)))
                (set '(err 1)))
  (check-equal? (⊢->>e '(+ (- 4 (err 1)) (err 2)))
                (set '(err 1))))

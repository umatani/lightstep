#lang racket/base
(require lightstep/base lightstep/syntax lightstep/inference
         (only-in "iswim.rkt" βv-rule subst)
         (only-in "e-iswim.rkt"
                  [E-ISWIM orig-E-ISWIM] ECxt FV δ δ-rule δerr-rule))

(module+ test (require rackunit))

;;=============================================================================
;; 8.1 Standard Reduction for Error ISWIM 

(define-language E-ISWIM #:super orig-E-ISWIM
  [Mre ∷= `(,V ,V) `(,(? oⁿ?) ,V ...) `(err ,(? b?))])

(define-inference (ẽ) #:super [(βv-rule) (δ-rule δ) (δerr-rule δ)])

(define-inference (⊢->e)
  #:do [(define rẽ (reducer-of (ẽ)))]
  #:forms (.... [`(,i →ẽ ,o) #:where o ← (rẽ i)])

  [#:when (M? m)
   `(,m →ẽ ,M′)
   -------------------------
   `(,(ECxt m) → ,(ECxt M′))]

  [#:when (not (equal? x e))
   `(err ,(? b? b)) ≔ e
   -------------------------------
   `(,(and x (ECxt e)) → (err ,b))])

(define step⊢->e (call-with-values (λ () (⊢->e)) compose1))
(define ⊢->>e (compose1 car (repeated step⊢->e)))

(define/match (evalₑˢ m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>e M)
    [(set (? b? b)) b]
    [(set `(λ ,X ,M)) 'function]
    [(set `(err ,(? b? b))) `(err ,b)]
    [x (error 'evalₑˢ "invalid answer: ~a" x)])]
  [_ (error 'evalₑˢ "invalid input: ~a" m)])

(module+ test
  (check-exn #rx"invalid input" (λ () (evalₑˢ '(+ 1 x))))
  (check-equal? (evalₑˢ '(+ ((λ x x) 8) 2)) 10)
  (check-equal? (evalₑˢ '((λ x x) (λ x x))) 'function)
  
  (check-equal? (evalₑˢ '(add1 (λ x x))) '(err 0))
  (check-equal? (evalₑˢ '(/ 3 0)) '(err 0))

  (check-equal? (step⊢->e '(+ (- 4 (err 1)) (err 2)))
                (set '(err 1)))
  (check-equal? (⊢->>e '(+ (- 4 (err 1)) (err 2)))
                (set '(err 1))))

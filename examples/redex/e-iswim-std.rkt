#lang racket/base
(require lightstep/base lightstep/syntax
         (only-in "iswim.rkt" βv-rule subst)
         (only-in "e-iswim.rkt"
                  [E-ISWIM orig-E-ISWIM] ECxt FV δ δ-rule δerr-rule))

(module+ test (require rackunit))

;;=============================================================================
;; 8.1 Standard Reduction for Error ISWIM 

(define-language E-ISWIM #:super orig-E-ISWIM)

(define-reduction (ẽ) #:super [(βv-rule) (δ-rule) (δerr-rule)])

(define step-ẽ (call-with-values (λ () (ẽ)) compose1))

(define-reduction (⊢->e)
  #:do [(define →ẽ (reducer-of (ẽ)))]
  [(ECxt m)
   #:when (M? m)
   M′ ← (→ẽ m)
   (ECxt M′)]
  [(and x (ECxt e))
   #:when (not (equal? x e))
   `(err ,L) ≔ e
   `(err ,L)])

(define step⊢->e (call-with-values (λ () (⊢->e)) compose1))
(define ⊢->>e (compose1 car (repeated step⊢->e)))

(define/match (evalₑˢ m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>e M)
    [(set (? b? b)) b]
    [(set `(λ ,X ,M)) 'function]
    [(set `(err ,L)) `(err ,L)]
    [x (error 'evalₑˢ "invalid answer: ~a" x)])]
  [_ (error 'evalₑˢ "invalid input: ~a" m)])

(module+ test
  (check-exn #rx"invalid input" (λ () (evalₑˢ '(+ 1 x))))
  (check-equal? (evalₑˢ '(+ ((λ x x) 8) 2)) 10)
  (check-equal? (evalₑˢ '((λ x x) (λ x x))) 'function)
  
  (check-equal? (evalₑˢ '(add1 (λ x x))) '(err add1))
  (check-equal? (evalₑˢ '(/ 3 0)) '(err 0))

  (check-equal? (step⊢->e '(+ (- 4 (err a)) (err b)))
                (set '(err a)))
  (check-equal? (⊢->>e '(+ (- 4 (err a)) (err b)))
                (set '(err a))))

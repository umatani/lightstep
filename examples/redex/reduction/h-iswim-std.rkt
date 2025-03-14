#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" βv-rule)
         (only-in "e-iswim.rkt" δ δ-rule)
         (only-in "h-iswim.rkt" [H-ISWIM orig-H-ISWIM] FV subst FCxt
                  δerr-rule return-rule catch-rule))
(provide ECxt)

(module+ test (require rackunit))

;;=============================================================================
;; 8.3 Standard Reduction for Handler ISWIM

(define-language H-ISWIM #:super orig-H-ISWIM)

(define-match-expander ECxt
  (syntax-parser
    [(ECxt p)
     #'(... (cxt ECxt [□ p]
                 `(,V ,□)
                 `(,□ ,M)
                 `(,(? oⁿ?) ,V ... ,□ ,M ...)
                 `(catch ,□ with (λ ,X ,M)) ;; NEW
                 ))]))

(define-reduction (h̃) #:super [(βv-rule) (δ-rule δ) (δerr-rule δ)
                                         (return-rule)
                                         (catch-rule)])

(define-reduction (⊢->h)
  #:do [(define →h̃ (reducer-of (h̃)))]

  [(ECxt `(,V₁ ,V₂))
   M ← (→h̃ `(,V₁ ,V₂))
   (ECxt M)]

  [(ECxt `(,(? oⁿ? oⁿ) ,V ...))
   M ← (→h̃ `(,oⁿ ,@V))
   (ECxt M)]

  [(ECxt `(catch ,V with (λ ,X ,M)))
   M′ ← (→h̃ `(catch ,V with (λ ,X ,M)))
   (ECxt M′)]

  [(ECxt `(catch (throw ,(? b? b)) with (λ ,X ,M)))
   M′ ← (→h̃ `(catch (throw ,b) with (λ ,X ,M)))
   (ECxt M′)]

  [(ECxt `(catch ,(and x (FCxt `(throw ,(? b? b)))) with (λ ,X ,M)))
   #:when (not (equal? x `(throw ,b)))
   (ECxt `(catch (throw ,b) with (λ ,X ,M)))]

  [(and x (FCxt `(throw ,(? b? b))))
   #:when (not (equal? x `(throw ,b)))
   `(throw ,b)])

(define step⊢->h (call-with-values (λ () (⊢->h)) compose1))
(define ⊢->>h (compose1 car (repeated step⊢->h)))

(define/match (evalₕˢ m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>h M)
    [(set (? b? b)) b]
    [(set `(λ ,X ,M)) 'function]
    [(set `(throw ,b)) `(err ,b)]
    [x (error 'evalₕˢ "invalid answer: ~a" x)])]
  [_ (error 'evalₕˢ "invalid input: ~a" m)])

(module+ test
  (check-exn #rx"invalid input" (λ () (evalₕˢ '(+ 1 x))))
  (check-equal? (evalₕˢ '(+ ((λ x x) 8) 2)) 10)
  (check-equal? (evalₕˢ '((λ x x) (λ x x))) 'function)
  
  (check-equal? (evalₕˢ '(add1 (λ x x))) '(err 0))
  (check-equal? (evalₕˢ '(/ 3 0)) '(err 0))

  (check-equal? (step⊢->h '(+ (- 4 (throw 1)) (throw 2)))
                (set '(throw 1)))
  (check-equal? (⊢->>h '(+ (- 4 (throw 1)) (throw 2)))
                (set '(throw 1)))

  (check-equal? (evalₕˢ '(catch (add1 (/ 3 0)) with (λ x (add1 x)))) 1)  
  (check-equal? (evalₕˢ '(catch (+ (* 4 2) (throw 3)) with (λ x (add1 x)))) 4))

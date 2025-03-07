#lang racket/base
(require lightstep/base lightstep/syntax lightstep/transformers
         (only-in "cc.rkt" □ [⊢->cc′ orig-⊢->cc′] mkCC)
         (only-in "e-iswim.rkt" δ [δ-rule orig-δ-rule])
         (only-in "h-iswim.rkt"
                  [H-ISWIM orig-H-ISWIM] FV subst FCxt
                  [δerr-rule orig-δerr-rule])
         (only-in "h-iswim-std.rkt" ECxt))

(module+ test (require rackunit))

;;=============================================================================
;; 8.3 The Handler CC Machine

(define-language H-ISWIM #:super orig-H-ISWIM)

;; to match the monad
(define-reduction (δ-rule) #:super [(orig-δ-rule δ)]
  #:monad (StateT #f (NondetT ID)))

(define-reduction (δerr-rule) #:super [(orig-δerr-rule δ)]
  #:monad (StateT #f (NondetT ID)))

(define-reduction (⊢->cc) #:super [(orig-⊢->cc′)]
  #:do [(define →δ    (reducer-of (δ-rule)))
        (define →δerr (reducer-of (δerr-rule)))]

  [`(,(? oⁿ? oⁿ) ,(? b? b) ...)
   (? b? b′) ← (→δ `(,oⁿ ,@b))
   b′
   "ccffi"]

  [M
   `(throw ,(? b? b))  ← (→δerr M)
   `(throw ,b)
   "cc7"]

  [`(throw ,(? b? b))
   (and x (FCxt (□))) ← get
   #:when (not (equal? x (□)))
   (put (□))
   `(throw ,b)
   "cc8"]

  [`(catch ,M with (λ ,X ,M′))
   (ECxt (□)) ← get
   (put (ECxt `(catch ,(□) with (λ ,X ,M′))))
   M
   "cc9"]

  [V
   (ECxt `(catch ,(□) with (λ ,X ,M))) ← get
   (put (ECxt (□)))
   V
   "cc10"]

  [`(throw ,(? b? b))
   (ECxt `(catch ,f with (λ ,X ,M))) ← get
   #:when (not (equal? f (□)))
   (put (ECxt `(catch ,(□) with (λ ,X ,M))))
   `(throw ,b)
   "cc11"]

  [`(throw ,(? b? b))
   (ECxt `(catch ,(□) with (λ ,X ,M))) ← get
   (put (ECxt (□)))
   `((λ ,X ,M) ,b)
   "cc12"])

(define step⊢->cc (let-values ([(mrun reducer) (⊢->cc)])
                    (match-λ
                     [(mkCC M ECxt)
                      (mrun ECxt (reducer M))])))
(define ⊢->>cc (compose1 car (repeated step⊢->cc)))

(define/match (evalcc+h m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>cc (mkCC M (□)))
     [(set (mkCC (? b? b) (□)))
      b]
     [(set (mkCC `(λ ,X ,M) (□)))
      'function]
     [(set (mkCC `(throw ,(? b? b)) (□)))
      `(err ,b)]
     [x (error 'evalcc+h "invalid final state: ~a" x)])]
  [_ (error 'evalcc+h "invalid input: ~a" m)])

(module+ test
  (check-exn #rx"invalid input" (λ () (evalcc+h '(+ 1 x))))
  (check-equal? (evalcc+h '(+ ((λ x x) 8) 2)) 10)
  (check-equal? (evalcc+h '((λ x x) (λ x x))) 'function)
  
  (check-equal? (evalcc+h '(add1 (λ x x))) '(err 0))
  (check-equal? (evalcc+h '(/ 3 0)) '(err 0))

  (check-equal? (⊢->>cc (mkCC '(+ (- 4 (throw 1)) (throw 2)) (□)))
                (set (mkCC '(throw 1) (□))))

  (check-equal? (evalcc+h '(catch (add1 (/ 3 0)) with (λ x (add1 x)))) 1)  
  (check-equal? (evalcc+h '(catch (+ (* 4 2) (throw 3)) with (λ x (add1 x)))) 4))

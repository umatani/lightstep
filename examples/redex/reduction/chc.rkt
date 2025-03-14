#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/transformers
         (only-in racket/match define-match-expander)
         (only-in "cc.rkt" □)
         (only-in "e-iswim.rkt" δ [δ-rule orig-δ-rule])
         (only-in "h-iswim.rkt"
                  [H-ISWIM orig-H-ISWIM] FV subst FCxt
                  [δerr-rule orig-δerr-rule]))

(module+ test (require rackunit))

;;=============================================================================
;; 8.3 The CHC Machine

(define-language H-ISWIM #:super orig-H-ISWIM
  [H ∷= (? list? λFCxts)])

;; to match the monad
(define-reduction (δ-rule) #:super [(orig-δ-rule δ)]
  #:monad (StateT #f (StateT #f (NondetT ID))))

(define-reduction (δerr-rule) #:super [(orig-δerr-rule δ)]
  #:monad (StateT #f (StateT #f (NondetT ID))))

(define-reduction (⊢->chc)
  #:monad (StateT #f (StateT #f (NondetT ID)))
  #:do [(define get-H (bind get (compose1 return car)))
        (define get-C (bind get (compose1 return cdr)))
        (define (put-H h)
          (do (cons _ c) ← get
              (put (cons h c))))
        (define (put-C c)
          (do (cons h _) ← get
              (put (cons h c))))

        (define →δ    (reducer-of (δ-rule)))
        (define →δerr (reducer-of (δerr-rule)))]

  [`(,M₁ ,M₂)
   #:when (not (V? M₁))
   (FCxt (□)) ← get-C
   (put-C (FCxt `(,(□) ,M₂)))
   M₁
   "chc1"]

  [`(,V ,M)
   #:when (not (V? M))
   (FCxt (□)) ← get-C
   (put-C (FCxt `(,V ,(□))))
   M
   "chc2"]

  [`(,(? oⁿ? oⁿ) ,V ... ,M ,M′ ...)
   #:when (not (V? M))
   (FCxt (□)) ← get-C
   (put-C (FCxt `(,oⁿ ,@V ,(□) ,@M′)))
   M
   "chc3"]

  [`((λ ,X ,M) ,V)
   (subst M X V)
   "chcfiᵥ"]

  [`(,(? oⁿ? oⁿ) ,(? b? b) ...)
   (? b? b′) ← (→δ `(,oⁿ ,@b))
   b′
   "chcffi"]

  [V
   (FCxt `(,V′ ,(□))) ← get-C
   (put-C (FCxt (□)))
   `(,V′ ,V)
   "chc4"]

  [V
   (FCxt `(,(□) ,M)) ← get-C
   (put-C (FCxt (□)))
   `(,V ,M)
   "chc5"]

  [V
   (FCxt `(,(? oⁿ? oⁿ) ,V′ ... ,(□) ,M ...)) ← get-C
   (put-C (FCxt (□)))
   `(,oⁿ ,@V′ ,V ,@M)
   "chc6"]

  [M
   `(throw ,(? b? b)) ← (→δerr M)
   `(throw ,b)
   "chc7"]

  [`(throw ,(? b? b))
   '() ← get-H
   f ← get-C
   #:when (not (equal? f (□)))
   (put-C (□))
   `(throw ,b)
   "chc8"]

  [`(catch ,M with (λ ,X ,M′))
   H ← get-H
   (FCxt (□)) ← get-C
   (put-H (cons `((λ ,X ,M′) ,(FCxt (□))) H))
   (put-C (□))
   M
   "chc9"]

  [V
   (cons `(,V′ ,(FCxt (□))) H) ← get-H
   f ← get-C
   #:when (equal? f (□))
   (put-H H)
   (put-C (FCxt (□)))
   V
   "chc10"]

  [`(throw ,(? b? b))
   H ← get-H
   f ← get-C
   #:when (and (not (null? H)) (not (equal? f (□))))
   (put-C (□))
   `(throw ,b)
   "chc11"]
  
  [`(throw ,(? b? b))
   (cons `(,V ,(FCxt (□))) H) ← get-H
   f ← get-C
   #:when (equal? f (□))
   (put-H H)
   (put-C (FCxt (□)))
   `(,V ,b)
   "chc12"])

(define-match-expander mkCHC
  (syntax-parser
    [(_ M H FCxt) #'(cons (cons M H) FCxt)])
  (syntax-parser
    [(_ M H FCxt) #'(cons (cons M H) FCxt)]))

(define step⊢->chc (let-values ([(mrun reducer) (⊢->chc)])
                    (match-λ
                     [(mkCHC M H FCxt)
                      (mrun FCxt H (reducer M))])))
(define ⊢->>chc (compose1 car (repeated step⊢->chc)))

(define/match (evalchc m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>chc (mkCHC M '() (□)))
     [(set (mkCHC (? b? b) '() (□)))
      b]
     [(set (mkCHC `(λ ,X ,M) '() (□)))
      'function]
     [(set (mkCHC `(throw ,(? b? b)) '() (□)))
      `(err ,b)]
     [x (error 'evalchc "invalid final state: ~a" x)])]
  [_ (error 'evalchc "invalid input: ~a" m)])


(module+ test
  (check-exn #rx"invalid input" (λ () (evalchc '(+ 1 x))))
  (check-equal? (evalchc '(+ ((λ x x) 8) 2)) 10)
  (check-equal? (evalchc '((λ x x) (λ x x))) 'function)
  
  (check-equal? (evalchc '(add1 (λ x x))) '(err 0))
  (check-equal? (evalchc '(/ 3 0)) '(err 0))

  (check-equal? (⊢->>chc (mkCHC '(+ (- 4 (throw 1)) (throw 2)) '() (□)))
                (set (mkCHC '(throw 1) '() (□))))

  (check-equal? (evalchc '(catch (add1 (/ 3 0)) with (λ x (add1 x)))) 1)  
  (check-equal? (evalchc '(catch (+ (* 4 2) (throw 3)) with (λ x (add1 x)))) 4))

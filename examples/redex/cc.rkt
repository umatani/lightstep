#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/transformers
         (only-in racket/unit invoke-unit)
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" [ISWIM orig-ISWIM] FV subst δ))

(module+ test (require rackunit))

(define-language ISWIM #:super orig-ISWIM)

;;=============================================================================
;; 6.1 The CC Machine

(define-match-expander ECxt
  (syntax-parser
    [(ECxt □:id)
     #'(ECxt □ #:hole □)]
    [(ECxt p #:hole □:id)
     #'(... (cxt ECxt [□ p]
                 `(,V ,□)
                 `(,□ ,M)
                 `(,(? oⁿ?) ,V ... ,□ ,M ...)))]))

(define-reduction (⊢->cc-rules)
  [`((,M₁ ,M₂) ,(ECxt □))
   #:when (not (V? M₁))
   `(,M₁ ,(ECxt `(,□ ,M₂)))
   "cc1"]

  [`((,V ,M) ,(ECxt □))
   #:when (not (V? M))
   `(,M ,(ECxt `(,V ,□)))
   "cc2"]

  [`((,(? oⁿ? oⁿ) ,V ... ,M₁ ,M ...) ,(ECxt □))
   #:when (not (V? M₁))
   `(,M₁ ,(ECxt `(,oⁿ ,@V ,□ ,@M)))
   "cc3"]

  [`(((λ ,X ,M) ,V) ,ECxt)
   `(,(subst M X V) ,ECxt)
   "ccfiᵥ"]

  [`((,(? oⁿ? oⁿ) ,(? b? b) ...) ,ECxt)
   `(,(δ oⁿ b) ,ECxt)
   "ccffi"]

  [`(,V ,(ECxt `(,V′ ,□) #:hole □))
   `((,V′ ,V) ,(ECxt □))
   "cc4"]

  [`(,V ,(ECxt `(,□ ,M) #:hole □))
   `((,V ,M) ,(ECxt □))
   "cc5"]

  [`(,V ,(ECxt `(,(? oⁿ? oⁿ) ,V′ ... ,□ ,M ...) #:hole □))
   `((,oⁿ ,@V′ ,V ,@M) ,(ECxt □))
   "cc6"])


(define-reduction (⊢->cc′-rules)
  #:monad (StateT #f (NondetT ID))

  [`(,M₁ ,M₂)
   #:when (not (V? M₁))
   (ECxt □) ← get
   (put (ECxt `(,□ ,M₂)))
   M₁ 
   "cc1"]

  [`(,V ,M)
   #:when (not (V? M))
   (ECxt □) ← get
   (put (ECxt `(,V ,□)))
   M
   "cc2"]

  [`(,(? oⁿ? oⁿ) ,V ... ,M₁ ,M ...)
   #:when (not (V? M₁))
   (ECxt □) ← get
   (put (ECxt `(,oⁿ ,@V ,□ ,@M)))
   M₁
   "cc3"]

  [`((λ ,X ,M) ,V)
   (subst M X V)
   "ccfiᵥ"]

  [`(,(? oⁿ? oⁿ) ,(? b? b) ...)
   (δ oⁿ b)
   "ccffi"]

  [V
   (ECxt `(,V′ ,□) #:hole □) ← get
   (put (ECxt □))
   `(,V′ ,V)
   "cc4"]

  [V
   (ECxt `(,□ ,M) #:hole □) ← get
   (put (ECxt □))
   `(,V ,M)
   "cc5"]

  [V
   (ECxt `(,(? oⁿ? oⁿ) ,V′ ... ,□ ,M ...) #:hole □) ← get
   (put (ECxt □))
   `(,oⁿ ,@V′ ,V ,@M)
   "cc6"])


(define ⊢->cc (call-with-values
               (λ () (invoke-unit (⊢->cc-rules)))
               compose1))
(define ⊢->>cc (compose1 car (repeated ⊢->cc)))

(define ⊢->cc′ (call-with-values
               (λ () (invoke-unit (⊢->cc′-rules)))
               (λ (mrun reducer)
                 (λ (ς) (mrun (cdr ς) (reducer (car ς)))))))
(define ⊢->>cc′ (compose1 car (repeated ⊢->cc′)))

(define □-cc #())

(define/match (evalcc m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>cc `(,M ,□-cc))
     [(set `(,(? b? b) ,□))
      #:when (equal? □ □-cc)
      b]
     [(set `((λ ,X ,(? M? N)) ,□))
      #:when (equal? □ □-cc)
      'function]
     [x (error 'evalcc "invalid final state: ~a" x)])]
  [_ (error 'evalcc "invalid input: ~a" m)])

(define/match (evalcc′ m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>cc′ (cons M □-cc))
     [(set (cons (? b? b) □))
      #:when (equal? □ □-cc)
      b]
     [(set (cons `(λ ,X ,(? M? N)) □))
      #:when (equal? □ □-cc)
      'function]
     [x (error 'evalcc′ "invalid final state: ~a" x)])]
  [_ (error 'evalcc′ "invalid input: ~a" m)])


(module+ test
  (check-equal? (⊢->>cc  `((((λ x x) (λ y y)) 1) ,□-cc))
                (set `(1 ,□-cc)))
  (check-equal? (⊢->>cc′ (cons '(((λ x x) (λ y y)) 1) □-cc))
                (set (cons 1 □-cc)))
  (check-equal? (⊢->>cc  `((+ (add1 2) (* 3 4)) ,□-cc))
                (set `(15 ,□-cc)))
  (check-equal? (⊢->>cc′ (cons '(+ (add1 2) (* 3 4)) □-cc))
                (set (cons 15 □-cc)))

  (check-equal? (evalcc '(+ (* 9 (↑ 2 3)) 3)) 75)
  (check-equal? (evalcc '(((λ f (λ x (f x))) (λ y (+ y y))) 8)) 16)
  (check-equal? (evalcc′ '(+ (* 9 (↑ 2 3)) 3)) 75)
  (check-equal? (evalcc′ '(((λ f (λ x (f x))) (λ y (+ y y))) 8)) 16))

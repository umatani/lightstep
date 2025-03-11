#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" δ)
         (only-in "s-iswim.rkt" [S-ISWIM orig-S-ISWIM] FV AV substs subst E))

(module+ test (require rackunit))

;;=============================================================================
;; 9.3 Revised Standard Reduction for State ISWIM

(define-language S-ISWIM #:super orig-S-ISWIM)

(define-match-expander Eₛ
  (syntax-parser
    [(Eₛ p)
     #'(cxt1 Eₛ [□ p]
             `(letrec ,x ,□)
             □)]))

(define-reduction (⊢->s2)
  #:do [(define (substs-Σ Σ xs ms)
          (for/map ([(x v) (in-map Σ)])
            (values (substs x xs ms) (substs v xs ms))))]

  [(Eₛ (E `((λ ,X ,M) ,V)))
   #:when (not (∈ X (AV M)))
   (Eₛ (E (subst M X V)))
   "s2fiᵥ"]

  [(Eₛ (E `(,(? oⁿ? oⁿ) ,V ...)))
   (Eₛ (E (δ oⁿ V)))
   "s2ffi"]

  [(Eₛ (E `((λ ,X ,M) ,V)))
   #:when (∈ X (AV M))
   (Eₛ (E `(letrec ,(↦ [X V]) ,M)))
   "s2fiₛ"]

  [(and x (E `(letrec ,Σ ,M)))
   #:when (not (equal? x `(letrec ,Σ ,M)))
   `(letrec ,Σ ,(E M))
   "s2liftE"]

  [`(letrec ,Σ ,(E `(letrec ,Σ′ ,M)))
   `(,X′ ...) ≔ (set→list (dom Σ′))
   `(,(? X? Y) ...) ≔ (map (symbol-not-in (dom Σ)) X′)
   `(letrec ,(⊔ Σ (substs-Σ Σ′ X′ Y)) ,(E (substs M X′ Y)))   
   "s2liftR"]

  [`(letrec ,Σ ,(E X))
   #:when (map-∈ X Σ)
   `(letrec ,Σ ,(E (Σ X)))
   "s2derefR"]

  [`(letrec ,Σ ,(E `(set ,X ,V)))
   #:when (map-∈ X Σ)
   `(letrec ,(Σ X V) ,(E (Σ X)))
   "s2assignR"])

(define step⊢->s2 (call-with-values (λ () (⊢->s2)) compose1))
(define ⊢->>s2 (compose1 car (repeated step⊢->s2)))

(define/match (evalₛ₂ m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>s2 M)
     [(set (or (? b? b) `(letrec ,(? Σ?) ,(? b? b)))) b]
     [(set (or `(λ ,X ,M) `(letrec ,(? Σ?) (λ ,X ,M)))) 'function]
     [x (error 'evalₛ₂ "invalid answer: ~a" x)])]
  [_ (error 'evalₛ₂ "invalid input: ~a" m)])



(module+ test
  (check-equal? (evalₛ₂ '((λ y (+ 1 ((λ x (* (add1 x) y)) (set y 3)))) 2))
                10)

  (check-equal? (evalₛ₂ `(+ 3 (letrec ,(↦ ['y 1])
                                ((λ z (+ z y)) 8))))
                12)

  (check-equal? (evalₛ₂ `((λ x (+ 3 (letrec ,(↦ ['y 1])
                                      ((λ z (+ z y))
                                       (set x (+ x 1))))))
                          0))
                4))

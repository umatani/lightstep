#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax
         (only-in "iswim.rkt" ISWIM βv-rule)
         (only-in "e-iswim.rkt" δ δ-rule)
         (only-in "h-iswim.rkt" [FV orig-FV] [subst orig-subst]
                  throw-rule return-rule δerr-rule))
(provide C-ISWIM FV subst FCxt)

(module+ test (require rackunit))

;;=============================================================================
;; 8.4 The Control ISWIM

(define-language C-ISWIM #:super ISWIM
  [M  ∷= ....
      `(throw ,(? b?))
      `(catch ,M₁ with (λ ,X₁ (λ ,X₂ ,M₂)))]
  [o² ∷= .... '/])

;; M → 𝒫(X)
(define/match (FV m) #:super orig-FV
  [`(catch ,M₁ with (λ ,X₁ (λ ,X₂ ,M₂)))
   (∪ (FV M₁) (FV `(λ ,X₁ (λ ,X₂ ,M₂))))])

;; M X M → M
(define/match (subst m₁ x₂ m₂) #:super orig-subst
  [(`(catch ,M with (λ ,X (λ ,X′ ,M′))) X₂ M₂)
   `(catch ,(subst M X₂ M₂) with ,(subst (λ ,X (λ ,X′ ,M′)) X₂ M₂))])

;; re-interpret M
(define-match-expander FCxt
  (syntax-parser
    [(FCxt p)
     #'(... (cxt FCxt [□ p]
                 `(,V ,□)
                 `(,□ ,M)
                 `(,(? oⁿ?) ,V ... ,□ ,M ...)))]))

;; re-interpret oⁿ, M, and modify catch
(define-nondet-match-expander Cxt′
  (λ (stx)
    (syntax-case stx ()
      [(Cxt′ □)
       #'(nondet-cxt Cxt′ □
                     ;`(λ ,X ,(? M? □)) ;; non-termination
                     `(,(? M? □) ,M)
                     `(,V ,(? M? □))
                     `(,(? oⁿ?) ,V (... ...) ,(? M? □) ,M (... ...))
                     `(catch ,(? M? □) with (λ ,X₁ (λ ,X₂ ,M)))
                     )])))

(define-nondet-match-expander Cxt
  (λ (stx)
    (syntax-case stx ()
      [(Cxt □)
       #'(nondet-cxt Cxt □
                     ;`(λ ,X ,(? M? □)) ;; non-termination
                     `(,(? M? □) ,M)
                     `(,V ,(? M? □))
                     `(,(? oⁿ?) ,V (... ...) ,(? M? □) ,M (... ...))
                     )])))

;; M --> M
(define-reduction (cntrl-rule)
  [`(catch ,(FCxt `(throw ,(? b? b))) with (λ ,X₁ (λ ,X₂ ,M)))
   X′ ≔ ((symbol-not-in (FV (FCxt 5))) 'Y)
   `(((λ ,X₁ (λ ,X₂ ,M)) ,b) (λ ,X′ ,(FCxt X′)))])

;; M --> M
(define-reduction (c′) #:super [(βv-rule) (δ-rule δ) (δerr-rule δ)
                                          (return-rule)
                                          (cntrl-rule)])

;; M --> M
(define-reduction (c) #:super [(c′) (throw-rule)])

;; M --> M
;; inside catch
(define-reduction (-->c′) #:super [(c′)]
  [(Cxt′ m)
   M′ ← (-->c′ m)
   (Cxt′ M′)])

;; M --> M
;; toplevel, i.e., outside catch context
(define-reduction (-->c) #:super [(c)]
  #:do [(define →-->c′ (reducer-of (-->c′)))]
  [(Cxt m)
   M′ ← (-->c m)
   (Cxt M′)]
  [(FCxt `(catch ,M₁ with (λ ,X₁ (λ ,X₂ ,M₂))))
   M₁′ ← (→-->c′ M₁)
   (FCxt `(catch ,M₁′ with (λ ,X₁ (λ ,X₂ ,M₂))))])

;; M → 𝒫(M)
(define step-->c (call-with-values (λ () (-->c)) compose1))
(define -->>c (compose1 car (repeated step-->c)))

;; M → (V ∪ ⊥)
(define/match (evalc m)
  [M
   #:when (∅? (FV M))
   (match (-->>c M)
    [(set (? b? b)) b]
    [(set `(λ ,X ,M)) 'function]
    [(set `(throw ,(? b? b))) `(err ,b)]
    [x (error 'evalc "invalid answer: ~s" x)])]
  [_ (error 'evalc "invalid input: ~s" m)])

(module+ test
  (check-exn #rx"invalid input" (λ () (evalc '(+ 1 x))))
  (check-equal? (evalc '(+ ((λ x x) 8) 2)) 10)
  (check-equal? (evalc '((λ x x) (λ x x))) 'function)
  
  (check-equal? (evalc '(add1 (λ x x))) '(err 0))
  (check-equal? (evalc '(/ 3 0)) '(err 0))

  (check-equal? (step-->c '(+ (- 4 (throw 1)) (throw 2)))
                (set '(+ (throw 1) (throw 2)) '(throw 1)))
  (check-equal? (-->>c '(+ (- 4 (throw 1)) (throw 2)))
                (set '(throw 1)))

  (check-equal? (evalc '(catch (add1 (/ 3 0))
                          with (λ x (λ f (f 10000))))) 10001))

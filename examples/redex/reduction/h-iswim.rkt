#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax
         (only-in "iswim.rkt" ISWIM [FV orig-FV] [subst orig-subst] βv-rule)
         (only-in "e-iswim.rkt" δ δ-rule))
(provide H-ISWIM FV subst FCxt
         throw-rule return-rule catch-rule δerr-rule)

(module+ test (require rackunit))

;;=============================================================================
;; 8.3 Handler ISWIM

(define-language H-ISWIM #:super ISWIM
  [M  ∷= ....
      `(throw ,(? b?))
      `(catch ,M₁ with (λ ,X ,M₂))]
  [o² ∷= .... '/])

;; M → 𝒫(X)
(define/match (FV m) #:super orig-FV
  [`(throw ,(? b?)) ∅]
  [`(catch ,M₁ with (λ ,X ,M₂))
   (∪ (FV M₁) (FV `(λ ,X ,M₂)))])

;; M X M → M
(define/match (subst m₁ x₂ m₂) #:super orig-subst
  [(`(throw ,(? b? b)) X₂ M₂)
   `(throw ,b)]
  [(`(catch ,M with (λ ,X ,M′)) X₂ M₂)
   `(catch ,(subst M X₂ M₂) with ,(subst (λ ,X ,M′) X₂ M₂))])

(define-match-expander FCxt
  (syntax-parser
    [(FCxt p)
     #'(... (cxt FCxt [□ p]
                 `(,V ,□)
                 `(,□ ,M)
                 `(,(? oⁿ?) ,V ... ,□ ,M ...)))]))

;; re-interpret oⁿ, M, and add catch
(define-nondet-match-expander Cxt
  (λ (stx)
    (syntax-case stx ()
      [(Cxt □)
       #'(nondet-cxt Cxt □
                     ;`(λ ,X ,(? M? □)) ;; non-termination
                     `(,(? M? □) ,M)
                     `(,V ,(? M? □))
                     `(,(? oⁿ?) ,V (... ...) ,(? M? □) ,M (... ...))
                     `(catch ,(? M? □) with (λ ,X ,M)))])))

;; M --> M
(define-reduction (throw-rule)
  [(and x (FCxt `(throw ,(? b? b))))
   #:when (not (equal? x `(throw ,b)))
   `(throw ,b)])

;; M --> M
(define-reduction (return-rule)
  [`(catch ,V with (λ ,X ,M))
   V])

;; M --> M
(define-reduction (catch-rule)
  [`(catch (throw ,(? b? b)) with (λ ,X ,M))
   `((λ ,X ,M) ,b)])

;; M --> M
(define-reduction (δerr-rule δ)
  [`(,(? oⁿ? oⁿ) ,(? b? b) ...)
   e ← (match (δ oⁿ b)
         [`(err ,(? b? b)) (return `(throw ,b))]
         [V         mzero])
   e]

  [`(,(? oⁿ? oⁿ) ,(? b? b) ... (λ ,X ,M) ,V ...)
   `(throw ,(length b))]

  [`(,(? b? b) ,V)
   `(throw ,b)])

;; M --> M
(define-reduction (h) #:super [(βv-rule) (δ-rule δ) (δerr-rule δ)
                                         (throw-rule)
                                         (return-rule)
                                         (catch-rule)])

;; M → 𝒫(M)
(define step-h (call-with-values (λ () (h)) compose1))

;; M --> M
(define-reduction (-->h) #:super [(h)]
  [(Cxt m)
   M′ ← (-->h m)
   (Cxt M′)])

;; M → 𝒫(M)
(define step-->h (call-with-values (λ () (-->h)) compose1))
(define -->>h (compose1 car (repeated step-->h)))

;; M → (V ∪ ⊥)
(define/match (evalₕ m)
  [M
   #:when (∅? (FV M))
   (match (-->>h M)
    [(set (? b? b)) b]
    [(set `(λ ,X ,M)) 'function]
    [(set `(throw ,(? b? b))) `(err ,b)]
    [x (error 'evalₕ "invalid answer: ~s" x)])]
  [_ (error 'evalₕ "invalid input: ~s" m)])

(module+ test
  (check-exn #rx"invalid input" (λ () (evalₕ '(+ 1 x))))
  (check-equal? (evalₕ '(+ ((λ x x) 8) 2)) 10)
  (check-equal? (evalₕ '((λ x x) (λ x x))) 'function)
  
  (check-equal? (evalₕ '(add1 (λ x x))) '(err 0))
  (check-equal? (evalₕ '(/ 3 0)) '(err 0))

  (check-equal? (step-->h '(+ (- 4 (throw 1)) (throw 2)))
                (set '(+ (throw 1) (throw 2)) '(throw 1)))
  (check-equal? (-->>h '(+ (- 4 (throw 1)) (throw 2)))
                (set '(throw 1)))

  (check-equal? (evalₕ '(catch (add1 (/ 3 0)) with (λ x (add1 x)))) 1)  
  (check-equal? (evalₕ '(catch (+ (* 4 2) (throw 3)) with (λ x (add1 x)))) 4))

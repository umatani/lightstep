#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/inference
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" ISWIM [FV orig-FV] [subst orig-subst] βv-rules)
         (only-in "e-iswim.rkt" δ δ-rules))
(provide H-ISWIM FV subst FCxt
         throw-rules return-rules catch-rules δerr-rules)

(module+ test (require rackunit))

;;=============================================================================
;; 8.3 Handler ISWIM

(define-language H-ISWIM #:super ISWIM
  [M  ∷= ....
      `(throw ,(? b?))
      `(catch ,M₁ with (λ ,X ,M₂))]
  [o² ∷= .... '/])

(define/match (FV m) #:super orig-FV
  [`(throw ,(? b?)) ∅]
  [`(catch ,M₁ with (λ ,X ,M₂))
   (∪ (FV M₁) (FV `(λ ,X ,M₂)))])

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

(define-inference (throw-rules)
  [#:when (not (equal? x `(throw ,b)))
   --------------------------------------------------
   `(,(and x (FCxt `(throw ,(? b? b)))) → (throw ,b))])

(define-inference (return-rules)
  [---------------------------------
   `((catch ,V with (λ ,X ,M)) → ,V)])

(define-inference (catch-rules)
  [------------------------------------------------------------
   `((catch (throw ,(? b? b)) with (λ ,X ,M)) → ((λ ,X ,M) ,b))])

(define-inference (δerr-rules δ)
  [e ← (match (δ oⁿ b)
         [`(err ,(? b? b)) (return `(throw ,b))]
         [V                mzero])
   ---------------------------------------------
   `((,(? oⁿ? oⁿ) ,(? b? b) ...) → ,e)          ]

  [---------------------------------------------------------------------
   `((,(? oⁿ? oⁿ) ,(? b? b) ... (λ ,X ,M) ,V ...) → (throw ,(length b)))]

  [------------------------------
   `((,(? b? b) ,V) → (throw ,b))])

(define-inference (h-rules) #:super [(βv-rules) (δ-rules δ) (δerr-rules δ)
                                                (throw-rules)
                                                (return-rules)
                                                (catch-rules)])

(define h (call-with-values (λ () (h-rules)) compose1))

(define-inference (-->h-rules) #:super [(h-rules)]
  [`(,m → ,M′)
   -----------------------
   `(,(Cxt m) → ,(Cxt M′))])

(define -->h (call-with-values (λ () (-->h-rules)) compose1))
(define -->>h (compose1 car (repeated -->h)))

(define/match (evalₕ m)
  [M
   #:when (∅? (FV M))
   (match (-->>h M)
    [(set (? b? b)) b]
    [(set `(λ ,X ,M)) 'function]
    [(set `(throw ,(? b? b))) `(err ,b)]
    [x (error 'evalₕ "invalid answer: ~a" x)])]
  [_ (error 'evalₕ "invalid input: ~a" m)])

(module+ test
  (check-exn #rx"invalid input" (λ () (evalₕ '(+ 1 x))))
  (check-equal? (evalₕ '(+ ((λ x x) 8) 2)) 10)
  (check-equal? (evalₕ '((λ x x) (λ x x))) 'function)
  
  (check-equal? (evalₕ '(add1 (λ x x))) '(err 0))
  (check-equal? (evalₕ '(/ 3 0)) '(err 0))

  (check-equal? (-->h '(+ (- 4 (throw 1)) (throw 2)))
                (set '(+ (throw 1) (throw 2)) '(throw 1)))
  (check-equal? (-->>h '(+ (- 4 (throw 1)) (throw 2)))
                (set '(throw 1)))

  (check-equal? (evalₕ '(catch (add1 (/ 3 0)) with (λ x (add1 x)))) 1)  
  (check-equal? (evalₕ '(catch (+ (* 4 2) (throw 3)) with (λ x (add1 x)))) 4))

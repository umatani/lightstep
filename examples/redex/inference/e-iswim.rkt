#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/inference
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" ISWIM [FV orig-FV] subst [δ orig-δ] βv-rules Cxt))
(provide E-ISWIM ECxt FV δ δ-rules δerr-rules)

(module+ test (require rackunit))

;;=============================================================================
;; 8.1 Error ISWIM

(define-language E-ISWIM #:super ISWIM
  [M   ∷= .... `(err ,(? b?))]
  [o²  ∷= .... '/])

;; re-interpret oⁿ?
(define-match-expander ECxt
  (syntax-parser
    [(ECxt p)
     #'(cxt ECxt [□ (and p (or `(,(? V?) ,(? V?))
                               `(,(? oⁿ?) ,(? V?) (... ...))))]
            `(,V ,□)
            `(,□ ,M)
            `(,(? oⁿ?) ,V (... ...) ,□ ,M (... ...)))]))

(define/match (FV m) #:super orig-FV
  [`(err ,(? b?)) ∅])

(define/match (δ o bs) #:super orig-δ
  [('/ `(,(? number? m) 0))
   '(err 0)]
  [('/ `(,(? number? m) ,(? number? n)))
   (/ m n)])

(define-inference (δ-rules δ)
  [v ← (match (δ oⁿ b)
         [`(err ,(? b?)) mzero]
         [V              (return V)])
   -----------------------------------
   `((,(? oⁿ? oⁿ) ,(? b? b) ...) → ,v)])

(define-inference (δerr-rules δ)
  [e ← (match (δ oⁿ b)
         [`(err ,(? b? b)) (return `(err ,b))]
         [V                mzero])
   --------------------------------------------
   `((,(? oⁿ? oⁿ) ,(? b? b) ...) → ,e)]

  [-------------------------------------------------------------------
   `((,(? oⁿ? oⁿ) ,(? b? b) ... (λ ,X ,M) ,V ...) → (err ,(length b)))]

  [----------------------------
   `((,(? b? b) ,V) → (err ,b))])

(define-inference (error-rules)
  [#:when (not (equal? x e))
   `(err ,(? b? b)) ≔ e
   -------------------------
   `(,(and x (ECxt e)) → (err ,b))])

(define-inference (w-rules) #:super [(δ-rules δ) (βv-rules)])
(define-inference (f-rules) #:super [(error-rules) (δerr-rules δ)])
(define-inference (e-rules) #:super [(w-rules) (f-rules)])

(define e (call-with-values (λ () (e-rules)) compose1))

(define-inference (-->e-rules) #:super [(e-rules)]
  [`(,m → ,M′)
   -----------------------
   `(,(Cxt m) → ,(Cxt M′))])

(define -->e (call-with-values (λ () (-->e-rules)) compose1))
(define -->>e (compose1 car (repeated -->e)))

(define/match (evalₑ m)
  [M
   #:when (∅? (FV M))
   (match (-->>e M)
    [(set (? b? b)) b]
    [(set `(λ ,X ,M)) 'function]
    [(set `(err ,(? b? b))) `(err ,b)]
    [x (error 'evalₑ "invalid answer: ~s" x)])]
  [_ (error 'evalₑ "invalid input: ~s" m)])

(module+ test
  (check-exn #rx"invalid input" (λ () (evalₑ '(+ 1 x))))
  (check-equal? (evalₑ '(+ ((λ x x) 8) 2)) 10)
  (check-equal? (evalₑ '((λ x x) (λ x x))) 'function)
  
  (check-equal? (evalₑ '(add1 (λ x x))) '(err 0))
  (check-equal? (evalₑ '(/ 3 0)) '(err 0))

  (check-equal? (-->e '(+ (- 4 (err 1)) (err 2)))
                (set '(+ (err 1) (err 2)) '(err 1)))
  (check-equal? (-->>e '(+ (- 4 (err 1)) (err 2)))
                (set '(err 1))))

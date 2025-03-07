#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" ISWIM [FV orig-FV] subst [δ orig-δ] βv-rule Cxt))
(provide E-ISWIM ECxt FV δ δ-rule δerr-rule)

(module+ test (require rackunit))

;;=============================================================================
;; 8.1 Error ISWIM

(define-language E-ISWIM #:super ISWIM
  [M   ∷= .... `(err ,L)]
  [L   ∷= (or (? b?) (? symbol?))]
  [o²  ∷= .... '/])

;; re-interpret oⁿ?
(define-match-expander ECxt
  (syntax-parser
    [(ECxt □)
     #'(cxt ECxt [□ (and □ (or `(,(? V?) ,(? V?))
                               `(,(? oⁿ?) ,(? V?) (... ...))))]
            `(,V ,□)
            `(,□ ,M)
            `(,(? oⁿ?) ,V (... ...) ,□ ,M (... ...)))]))

(define/match (FV m) #:super orig-FV
  [`(err ,L) ∅])

(define/match (δ o bs) #:super orig-δ
  [('/ `(,(? number? m) 0))
   '(err 0)]
  [('/ `(,(? number? m) ,(? number? n)))
   (/ m n)])

(define-reduction (δ-rule δ)
  [`(,(? oⁿ? oⁿ) ,(? b? b) ...)
   v ← (match (δ oⁿ b)
         [`(err ,L) mzero]
         [V         (return V)])
   v])

(define-reduction (δerr-rule δ)
  [`(,(? oⁿ? oⁿ) ,(? b? b) ...)
   e ← (match (δ oⁿ b)
          [`(err ,L) (return `(err ,L))]
          [V         mzero])
   e]

  [`(,(? oⁿ? oⁿ) ,(? b? b) ... (λ ,X ,M) ,V ...)
   `(err ,oⁿ)]

  [`(,(? b? b) ,V)
   `(err ,b)])

(define-reduction (error-rule)
  [(and x (ECxt e))
   #:when (not (equal? x e))
   `(err ,L) ≔ e
   `(err ,L)])

(define-reduction (w) #:super [(δ-rule δ) (βv-rule)])
(define-reduction (f) #:super [(error-rule) (δerr-rule δ)])
(define-reduction (e) #:super [(w) (f)])

(define step-e (call-with-values (λ () (e)) compose1))

(define-reduction (-->e) #:super [(e)]
  [(Cxt m)
   M′ ← (-->e m)
   (Cxt M′)])

(define step-->e (call-with-values (λ () (-->e)) compose1))
(define -->>e (compose1 car (repeated step-->e)))

(define/match (evalₑ m)
  [M
   #:when (∅? (FV M))
   (match (-->>e M)
    [(set (? b? b)) b]
    [(set `(λ ,X ,M)) 'function]
    [(set `(err ,L)) `(err ,L)]
    [x (error 'evalₑ "invalid answer: ~a" x)])]
  [_ (error 'evalₑ "invalid input: ~a" m)])

(module+ test
  (check-exn #rx"invalid input" (λ () (evalₑ '(+ 1 x))))
  (check-equal? (evalₑ '(+ ((λ x x) 8) 2)) 10)
  (check-equal? (evalₑ '((λ x x) (λ x x))) 'function)
  
  (check-equal? (evalₑ '(add1 (λ x x))) '(err add1))
  (check-equal? (evalₑ '(/ 3 0)) '(err 0))

  (check-equal? (step-->e '(+ (- 4 (err a)) (err b)))
                (set '(+ (err a) (err b)) '(err a)))
  (check-equal? (-->>e '(+ (- 4 (err a)) (err b)))
                (set '(err a))))

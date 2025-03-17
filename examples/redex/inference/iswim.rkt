#lang racket/base
(require (for-syntax racket/base)
         lightstep/base lightstep/syntax lightstep/inference
         (only-in lightstep/monad mapM)
         (prefix-in lam: (only-in "lam.rkt" LAM FV subst)))
(provide ISWIM FV subst βv-rules δ δ-rules v-rules Cxt)

(module+ test (require rackunit))

;;=============================================================================
;; 4.1 ISWIM Expressions

(define-syntax-rule (define-iswim-language L r ...)
  (define-language L #:super lam:LAM
    [M ∷= ....
       (? b?)
       `(,(? oⁿ?) ,M (... ...))]
    [V ∷= (? b?) X `(λ ,X ,M)]
    r ...))

(define-iswim-language ISWIM
  [KWD ∷= .... (? o¹?) (? o²?)]
  [b ∷= (? number?)]
  [oⁿ ∷= (? o¹?) (? o²?)]
  [o¹ ∷= 'add1 'sub1 'iszero]
  [o² ∷= '+ '- '* '↑])

(module+ test
  (check-true  (M? 1))
  (check-true  (M? '(↑ 1 2)))
  (check-false (M? '(/ 1 2))))

;; M → 𝒫(X)
(define/match (FV m) #:super lam:FV
  [(? b?) ∅]
  [`(,(? oⁿ?) ,M ...)
   (apply ∪ (map FV M))])

(module+ test
  (check-equal? (FV 'x)               (set 'x))
  (check-equal? (FV '(x (y x)))       (set 'x 'y))
  (check-equal? (FV '(λ x (x y)))     (set 'y))
  (check-equal? (FV '(z (λ z z)))     (set 'z))
  (check-equal? (FV 123)              ∅)
  (check-equal? (FV '(↑ (f x) (g 1))) (set 'f 'x 'g)))

;; M X M → M
(define/match (subst m₁ x₂ m₂) #:super lam:subst
  [((? b? b) X₂ M₂) b]
  [(`(,(? oⁿ? oⁿ) ,M ...) X₂ M₂)
   `(,oⁿ ,@(map (λ (m) (subst m X₂ M₂)) M))])


;;=============================================================================
;; 4.2  Calculating with ISWIM

;; M --> M
(define-inference (βv-rules)
  [----------------------------------
   `(((λ ,X ,M) ,V) → ,(subst M X V))])

;; oⁿ List(b) → V
(define/match (δ o bs)
  [('add1 `(,(? number? m)))
   (add1 m)]
  [('sub1 `(,(? number? m)))
   (sub1 m)]
  [('iszero `(0))
   '(λ x (λ y x))]
  [('iszero `(,(? number? n)))
   #:when (not (zero? n))
   '(λ x (λ y y))]

  [('+ `(,(? number? m) ,(? number? n)))
   (+ m n)]
  [('- `(,(? number? m) ,(? number? n)))
   (- m n)]
  [('* `(,(? number? m) ,(? number? n)))
   (* m n)]
  [('↑ `(,(? number? m) ,(? number? n)))
   (expt m n)])

;; M M M → M
(define (IF0 L M N)
  (let ([X ((symbol-not-in (FV M) (FV N)) 'if0)])
    `((((iszero ,L) (λ ,X ,M)) (λ ,X ,N)) 0)))

;; M --> V
(define-inference (δ-rules δ)
  [------------------------------------------
   `((,(? oⁿ? oⁿ) ,(? b? b) ...) → ,(δ oⁿ b))])

;; M --> M
(define-inference (v-rules) #:super [(βv-rules) (δ-rules δ)])

;; M → 𝒫(M)
(define v (call-with-values (λ () (v-rules)) compose1))

;; ECxt of iswim-std.rkt is same, but deterministic
(define-nondet-match-expander Cxt
  (λ (stx)
    (syntax-case stx ()
      [(Cxt □)
       #'(nondet-cxt Cxt □
                     ;`(λ ,X ,(? M? □)) ;; non-termination
                     `(,(? M? □) ,M)
                     `(,V ,(? M? □))
                     `(,(? oⁿ?) ,V (... ...) ,(? M? □) ,M (... ...)))])))

;; M --> M
(define-inference (-->v-rules) #:super [(v-rules)]
  [`(,m → ,M′)
   -----------------------
   `(,(Cxt m) → ,(Cxt M′))])

;; M → 𝒫(M)
(define -->v (call-with-values (λ () (-->v-rules)) compose1))
(define -->>v (compose1 car (repeated -->v)))

(module+ test
  (check-equal? (-->>v '((λ w (- (w 1) 5))
                         ((λ x (x 10)) (λ y (λ z (+ z y))))))
                (set 6))

  (check-equal? (-->>v (IF0 0 1 2)) (set 1))
  (check-equal? (-->>v (IF0 -1 1 2)) (set 2)))

;;=============================================================================
;; 4.4  The Yv Combinator

(define Y '(λ f ((λ x (f (x x))) (λ x (f (x x))))))

#;
(define Yv '(λ f (λ y (((λ x (λ z ((f (λ p ((x x) p))) z)))
                        (λ x (λ z ((f (λ p ((x x) p))) z)))) y))))
(define Yv '(λ f (λ x (((λ g (f (λ x ((g g) x))))
                        (λ g (f (λ x ((g g) x))))) x))))

(module+ test
  (define SUM `(,Yv (λ s (λ n ,(IF0 'n '0 '(+ n (s (sub1 n))))))))
  ;(-->>v `(,Y ,SUM))
  (check-equal? (-->>v `(,SUM 10)) (set 55)))

;;=============================================================================
;; 4.5  Evaluation

;; M → V
(define/match (evalᵥ m)
  [M
   #:when (∅? (FV M))
   (match (-->>v M)
    [(set (? b? b)) b]
    [(set `(λ ,X ,M)) 'function]
    [x (error 'evalᵥ "invalid answer: ~s" x)])]
  [_ (error 'evalᵥ "invalid input: ~s" m)])

(module+ test
  (check-exn #rx"invalid input" (λ () (evalᵥ '(+ 1 x))))
  (check-equal? (evalᵥ '(+ ((λ x x) 8) 2)) 10)
  (check-equal? (evalᵥ '((λ x x) (λ x x))) 'function)
  (check-exn #rx"invalid answer" (λ () (evalᵥ '(add1 (λ x x))))))

;;=============================================================================
;; 4.6  Consistency

;; M --> M
(define-inference (↪v-rules)
  #:forms ([`(,i:i ↪ ,o:o) #:where o ← (↪v i)])

  [----------
   `(,M ↪ ,M)]

  [------------------------------------------
   `((,(? oⁿ? oⁿ) ,(? b? b) ...) ↪ ,(δ oⁿ b))]

  [   `(,M ↪ ,M′)      `(,V ↪ ,V′)
   ------------------------------------
   `(((λ ,X ,M) ,V) ↪ ,(subst M′ X V′))]

  [`(,M₁ ↪ ,M₁′)    `(,M₂ ↪ ,M₂′)
   -------------------------------
     `((,M₁ ,M₂) ↪ (,M₁′ ,M₂′))   ]

  [       `(,M ↪ ,M′)
   -------------------------
   `((λ ,X ,M) ↪ (λ ,X ,M′))]

  [`(,M′ ...) ← (mapM ↪v M)
   ------------------------------------
   `((,(? oⁿ? oⁿ) ,M ...) ↪ (,oⁿ ,@M′))])

;; M → 𝒫(M)
(define ↪v (call-with-values (λ () (↪v-rules)) compose1))

(module+ test
  ;; (for ([m′ (step-↪v '((λ x (x x)) (λ y ((λ x x) (λ x x)))))])
  ;;   (printf "~s\n" m′))
  ;; (for ([m′ (step-↪v '((λ y ((λ x x) (λ x x))) (λ y ((λ x x) (λ x x)))))])
  ;;   (printf "~s\n" m′))
  )

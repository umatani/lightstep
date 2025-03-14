#lang racket/base
(require (for-syntax racket/base)
         lightstep/base lightstep/syntax)
(provide LAM FV subst α)

(module+ test (require rackunit))

;;=============================================================================
;; 3.2 λ-Calculus: Syntax and Reductions

(define-language LAM
  [M ∷=
     X
     `(λ ,X ,M)
     `(,M₁ ,M₂)]
  [X ∷= (? symbol? (? (compose1 not KWD?)))]
  [KWD ∷= 'λ])

(module+ test
  (check-true (M? 'x))
  (check-true (M? '(x y)))
  (check-true (M? '(λ x x)))
  (check-true (M? '((x y) (z w))))
  (check-true (M? '(λ y (λ z y))))
  (check-true (M? '((λ y (y y)) (λ y (y y))))))

(define/match (FV m)
  [X          (set X)]
  [`(λ ,X ,M) (set-remove (FV M) X)]
  [`(,M₁ ,M₂) (∪ (FV M₁) (FV M₂))])

(module+ test
  (check-equal? (FV 'x)           (set 'x))
  (check-equal? (FV '(x (y x)))   (set 'x 'y))
  (check-equal? (FV '(λ x (x y))) (set 'y))
  (check-equal? (FV '(z (λ z z))) (set 'z)))

(define/match (subst m₁ x m₂)
  [(X₁ X₂ M₂)
   #:when (eq? X₁ X₂)
   M₂]
  [(X₁ X₂ M₂)
   X₁]
  [(`(λ ,X₁ ,M₁) X₂ M₂)
   #:when (eq? X₁ X₂)
   `(λ ,X₁ ,M₁)]
  [(`(λ ,X₁ ,M₁) X₂ M₂)
   (let ([X₃ ((symbol-not-in (FV `(λ ,X₁ ,M₁)) (FV M₂)) X₁)])
     `(λ ,X₃ ,(subst (subst M₁ X₁ X₃) X₂ M₂)))]
  [(`(,M₁₁ ,M₁₂) X₂ M₂)
   `(,(subst M₁₁ X₂ M₂) ,(subst M₁₂ X₂ M₂))])

(module+ test
  (check-equal? (subst 'x 'x '(λ y y)) '(λ y y))
  (check-equal? (subst 'z 'x '(λ y y)) 'z)
  (check-equal? (subst '(λ x x) 'x '(λ y y)) '(λ x x))
  (check-equal? (subst '(λ y (x y)) 'x '(λ y y)) '(λ y ((λ y y) y)))
  ;; (subst '(λ y (x y)) 'x '(λ x y))
  )

(define-nondet-match-expander Cxt
  (λ (stx)
    (syntax-case stx ()
      [(Cxt □)
       #'(nondet-cxt Cxt □
                     `(λ ,X ,(? M? □))
                     `(,(? M? □) ,M)
                     `(,M ,(? M? □)))])))

(define-reduction (-->gen r)
  [(Cxt m)
   M′ ← (r m)
   (Cxt M′)])

(define-reduction (α)
  [`(λ ,X₁ ,M)
   X₂ ≔ ((symbol-not-in (FV M)) X₁)
   `(λ ,X₂ ,(subst M X₁ X₂))
   "α"])

(define step-α (call-with-values (λ () (α)) compose1))

(define-reduction (-->α) #:super [(-->gen -->α)]
  #:do [(define →α (reducer-of (α)))]
  [M
   M′ ← (→α M)
   M′
   "α"])

(define step-->α (call-with-values (λ () (-->α)) compose1))

(define-reduction (β)
  [`((λ ,X ,M₁) ,M₂)
   (subst M₁ X M₂)
   "β"])

(define step-β (call-with-values (λ () (β)) compose1))

(define-reduction (-->β) #:super [(-->gen -->β)]
  #:do [(define →β (reducer-of (β)))]
  [M
   M′ ← (→β M)
   M′
   "β"])

(define step-->β (call-with-values (λ () (-->β)) compose1))

(define-reduction (η)
  [`(λ ,X (,M ,X′))
   #:when (eq? X X′)
   #:when (not (∈ X (FV M)))
   M
   "η"])

(define step-η (call-with-values (λ () (η)) compose1))

(define-reduction (-->η) #:super [(-->gen -->η)]
  #:do [(define →η (reducer-of (η)))]
  [M
   M′ ← (→η M)
   M′
   "η"])

(define step-->η (call-with-values (λ () (-->η)) compose1))

(define-reduction (n) #:super [#;(α) (β) (η)])

(define step-n (call-with-values (λ () (n)) compose1))

(define-reduction (-->n) #:super [(-->gen -->n)]
  #:do [(define →n (reducer-of (n)))]
  [M
   M′ ← (→n M)
   M′
   "n"])

(define step-->n (call-with-values (λ () (-->n)) compose1))

(define -->>n (compose1 car (repeated step-->n)))

(module+ test
  (check-equal? (-->>n '(λ x ((λ z z) x))) (set '(λ x x) '(λ z z)))
  (check-equal? (-->>n '((λ x ((λ z z) x)) (λ x x))) (set '(λ x x)))

  (check-equal? (-->>n '(λ x x)) (set '(λ x x)))
  (check-equal? (-->>n '(((λ x (λ y (y x))) (λ y y)) (λ x (x x))))
                (set '(λ y y)))
  (check-equal? (-->>n '((λ x (λ y (y x))) ((λ x (x x)) (λ x (x x)))))
                ∅))

;;=============================================================================
;; 3.3 Encoding Booleans

(define TRUE  '(λ x (λ y x)))
(define FALSE '(λ x (λ y y)))
(define IF    '(λ v (λ t (λ f ((v t) f)))))

(module+ test
  (check-equal? (-->>n̅ `(((,IF ,TRUE ) M) N)) (set 'M))
  (check-equal? (-->>n̅ `(((,IF ,FALSE) M) N)) (set 'N)))

;;=============================================================================
;; 3.4 Encoding Pairs

(define (PAIR m n) `(λ s ((s ,m) ,n)))
(define MKPAIR `(λ x (λ y ,(PAIR 'x 'y))))
(define FST `(λ p (p ,TRUE)))
(define SND `(λ p (p ,FALSE)))

(module+ test
  (check-equal? (-->>n̅ `(,FST ((,MKPAIR M) N))) (set 'M))
  (check-equal? (-->>n̅ `(,SND ((,MKPAIR M) N))) (set 'N)))

;;=============================================================================
;; 3.5 Encoding Numbers

(define (MKNUM n)
  (let loop ([n n]
             [body 'x])
    (if (zero? n)
      `(λ f (λ x ,body))
      (loop (sub1 n) `(f ,body)))))

(define ADD1 '(λ n (λ f (λ x (f ((n f) x))))))
(define ADD `(λ n (λ m ((m ,ADD1) n))))
(define ISZERO `(λ n ((n (λ x ,FALSE)) ,TRUE)))

(define (WRAP f) `(λ p ,(PAIR FALSE
                              `(((,IF (,FST p)) (,SND p)) (,f (,SND p))))))
(define SUB1 `(λ n (λ f (λ x (,SND ((n ,(WRAP 'f)) ,(PAIR TRUE 'x)))))))

(module+ test
  (check-equal? (-->>n̅ `(,ADD1 ,(MKNUM 1))) (set (MKNUM 2)))
  (check-equal? (-->>n̅ `((,ADD ,(MKNUM 2)) ,(MKNUM 3))) (set (MKNUM 5)))
  (check-equal? (-->>n̅ `(,ISZERO ,(MKNUM 1))) (set FALSE))
  (check-equal? (-->>n̅ `(,SUB1 ,(MKNUM 3))) (set (MKNUM 2))))

;;=============================================================================
;; 3.7 Recursion

(define MKMULT0 `(λ t (λ n (λ m
                             (((,IF (,ISZERO n)) ,(MKNUM 0))
                              ((,ADD m) ((t (,SUB1 n)) m)))))))

(define MKMULT `(λ t (λ n (λ m
                            (((,IF (,ISZERO n)) ,(MKNUM 0))
                             ((,ADD m) (((t t) (,SUB1 n)) m)))))))
(define MULT `(,MKMULT ,MKMULT))

(module+ test
  (check-equal? (-->>n̅ `((,MULT ,(MKNUM 0)) m)) (set (MKNUM 0)))

  ;; slow
  ;(check-equal? (-->>n̅ `((,MULT ,(MKNUM 2)) ,(MKNUM 2))) (set (MKNUM 4)))
  )

(define MKMK '(λ k (λ t (t ((k k) t)))))
(define MK `(,MKMK ,MKMK))

(module+ test
  (check-equal? (-->>n̅ `(((,MK ,MKMULT0) ,(MKNUM 0)) ,(MKNUM 2)))
                (set (MKNUM 0)))
  (check-equal? (-->>n̅ `(((,MK ,MKMULT0) ,(MKNUM 1)) ,(MKNUM 2)))
                (set (MKNUM 2))))

(define Y '(λ f ((λ x (f (x x))) (λ x (f (x x))))))

(define SUM `(,Y (λ s (λ n (((,IF (,ISZERO n)) ,(MKNUM 0))
                            ((,ADD n) (s (,SUB1 n))))))))

(module+ test
  ;; slow
  ;(check-equal? (-->>n̅ `(,SUM ,(MKNUM 2))) (set (MKNUM 3)))
  )

;;=============================================================================
;; 3.9 Normal Forms and Reduction Strategies

(define Ω '((λ x (x x)) (λ x (x x))))

(define-reduction (-->n̅)
  #:do [(define →β (reducer-of (β)))
        (define →η (reducer-of (η)))]
  [M
   M′ ← (→β M)
   M′]
  [M
   M′ ← (→η M)
   M′]
  [`(λ ,X ,M)
   #:when (∅? (step-η `(λ ,X ,M)))
   M′ ← (-->n̅ M)
   `(λ ,X ,M′)]
  [`(,M₁ ,M₂)
   #:when (∅? (step-β `(,M₁ ,M₂)))
   M₁′ ← (-->n̅ M₁)
   `(,M₁′ ,M₂)]
  [`(,M₁ ,M₂)
   #:when (∅? (→β `(,M₁ ,M₂)))
   #:when (∅? (-->n̅ M₁))
   M₂′ ← (-->n̅ M₂)
   `(,M₁ ,M₂′)])

(define step-->n̅ (call-with-values (λ () (-->n̅)) compose1))

(define -->>n̅ (compose1 car (repeated step-->n̅)))

(module+ test
  (check-equal? (-->>n̅ `((λ y (λ z z)) ,Ω)) (set '(λ z z))))

#lang racket/base
(require (for-syntax racket/base)
         lightstep/base lightstep/syntax lightstep/inference)
(provide LAM FV subst α-rules)

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

;; M → 𝒫(X)
(define/match (FV m)
  [X          (set X)]
  [`(λ ,X ,M) (set-remove (FV M) X)]
  [`(,M₁ ,M₂) (∪ (FV M₁) (FV M₂))])

(module+ test
  (check-equal? (FV 'x)           (set 'x))
  (check-equal? (FV '(x (y x)))   (set 'x 'y))
  (check-equal? (FV '(λ x (x y))) (set 'y))
  (check-equal? (FV '(z (λ z z))) (set 'z)))

;; M X M → M
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

;; M --> M
(define-inference (-->gen-rules reducer)
  #:forms (.... [`(,i →ᵣ ,o) #:where o ← (reducer i)])

  [`(,m →ᵣ ,M′)
   -----------------------
   `(,(Cxt m) → ,(Cxt M′))])

;; M --> M
(define-inference (α-rules)
  [X₂ ≔ ((symbol-not-in (FV M)) X₁)
   ---------------------------------------- "α"
   `((λ ,X₁ ,M) → (λ ,X₂ ,(subst M X₁ X₂)))    ])

;; M → 𝒫(M)
(define α (call-with-values (λ () (α-rules)) compose1))

;; M --> M
(define-inference (-->α-rules) #:super [(-->gen-rules -->α-rules)]
  #:do [(define rα (reducer-of (α-rules)))]
  #:forms (.... [`(,i →α ,o) #:where o ← (rα i)])

  [`(,M →α ,M′)
   ------------ "α"
   `(,M → ,M′)     ])

;; M → 𝒫(M)
(define -->α (call-with-values (λ () (-->α-rules)) compose1))

;; M --> M
(define-inference (β-rules)
  [-------------------------------------- "β"
   `(((λ ,X ,M₁) ,M₂) → ,(subst M₁ X M₂))    ])

;; M → 𝒫(M)
(define β (call-with-values (λ () (β-rules)) compose1))

;; M --> M
(define-inference (-->β-rules) #:super [(-->gen-rules -->β-rules)]
  #:do [(define rβ (reducer-of (β-rules)))]
  #:forms (.... [`(,i →β ,o) #:where o ← (rβ i)])
  
  [`(,M →β ,M′)
   ------------ "β"
   `(,M → ,M′)     ])

;; M → 𝒫(M)
(define -->β (call-with-values (λ () (-->β-rules)) compose1))

;; M --> M
(define-inference (η-rules)
  [#:when (eq? X X′)
   #:when (not (∈ X (FV M)))
   ------------------------- "η"
   `((λ ,X (,M ,X′)) → ,M)      ])

;; M → 𝒫(M)
(define η (call-with-values (λ () (η-rules)) compose1))

;; M --> M
(define-inference (-->η-rules) #:super [(-->gen-rules -->η-rules)]
  #:do [(define rη (reducer-of (η-rules)))]
  #:forms (.... [`(,i →η ,o) #:where o ← (rη i)])
  [`(,M →η ,M′)
   ------------ "η"
   `(,M → ,M′)     ])

;; M → 𝒫(M)
(define -->η (call-with-values (λ () (-->η-rules)) compose1))

;; M --> M
(define-inference (n-rules) #:super [#;(α-rules) (β-rules) (η-rules)])

;; M → 𝒫(M)
(define n (call-with-values (λ () (n-rules)) compose1))

;; M --> M
(define-inference (-->n-rules) #:super [(-->gen-rules -->n-rules)]
  #:do [(define rn (reducer-of (n-rules)))]
  #:forms (.... [`(,i →n ,o) #:where o ← (rn i)])
  [`(,M →n ,M′)
   ------------ "n"
   `(,M → ,M′)     ])

;; M → 𝒫(M)
(define -->n (call-with-values (λ () (-->n-rules)) compose1))
(define -->>n (compose1 car (repeated -->n)))

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

;; M
(define TRUE  '(λ x (λ y x)))
(define FALSE '(λ x (λ y y)))
(define IF    '(λ v (λ t (λ f ((v t) f)))))

(module+ test
  (check-equal? (-->>n̅ `(((,IF ,TRUE ) M) N)) (set 'M))
  (check-equal? (-->>n̅ `(((,IF ,FALSE) M) N)) (set 'N)))

;;=============================================================================
;; 3.4 Encoding Pairs

;; M M → M
(define (PAIR m n) `(λ s ((s ,m) ,n)))
;; M
(define MKPAIR `(λ x (λ y ,(PAIR 'x 'y))))
(define FST `(λ p (p ,TRUE)))
(define SND `(λ p (p ,FALSE)))

(module+ test
  (check-equal? (-->>n̅ `(,FST ((,MKPAIR M) N))) (set 'M))
  (check-equal? (-->>n̅ `(,SND ((,MKPAIR M) N))) (set 'N)))

;;=============================================================================
;; 3.5 Encoding Numbers

;; M → M
(define (MKNUM n)
  (let loop ([n n]
             [body 'x])
    (if (zero? n)
      `(λ f (λ x ,body))
      (loop (sub1 n) `(f ,body)))))
;; M
(define ADD1 '(λ n (λ f (λ x (f ((n f) x))))))
(define ADD `(λ n (λ m ((m ,ADD1) n))))
(define ISZERO `(λ n ((n (λ x ,FALSE)) ,TRUE)))
;; M → M
(define (WRAP f) `(λ p ,(PAIR FALSE
                              `(((,IF (,FST p)) (,SND p)) (,f (,SND p))))))
;; M
(define SUB1 `(λ n (λ f (λ x (,SND ((n ,(WRAP 'f)) ,(PAIR TRUE 'x)))))))

(module+ test
  (check-equal? (-->>n̅ `(,ADD1 ,(MKNUM 1))) (set (MKNUM 2)))
  (check-equal? (-->>n̅ `((,ADD ,(MKNUM 2)) ,(MKNUM 3))) (set (MKNUM 5)))
  (check-equal? (-->>n̅ `(,ISZERO ,(MKNUM 1))) (set FALSE))
  (check-equal? (-->>n̅ `(,SUB1 ,(MKNUM 3))) (set (MKNUM 2))))

;;=============================================================================
;; 3.7 Recursion

;; M
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

;; M
(define MKMK '(λ k (λ t (t ((k k) t)))))
(define MK `(,MKMK ,MKMK))

(module+ test
  (check-equal? (-->>n̅ `(((,MK ,MKMULT0) ,(MKNUM 0)) ,(MKNUM 2)))
                (set (MKNUM 0)))
  (check-equal? (-->>n̅ `(((,MK ,MKMULT0) ,(MKNUM 1)) ,(MKNUM 2)))
                (set (MKNUM 2))))

;; M
(define Y '(λ f ((λ x (f (x x))) (λ x (f (x x))))))
(define SUM `(,Y (λ s (λ n (((,IF (,ISZERO n)) ,(MKNUM 0))
                            ((,ADD n) (s (,SUB1 n))))))))

(module+ test
  ;; slow
  ;(check-equal? (-->>n̅ `(,SUM ,(MKNUM 2))) (set (MKNUM 3)))
  )

;;=============================================================================
;; 3.9 Normal Forms and Reduction Strategies

;; M
(define Ω '((λ x (x x)) (λ x (x x))))

;; M --> M
(define-inference (-->n̅-rules)
  #:do [(define rβ (reducer-of (β-rules)))
        (define rη (reducer-of (η-rules)))]
  #:forms ([`(,i:i →n̅ ,o:o) #:where o ← (-->n̅-rules i)]
           [`(,i   →β ,o  ) #:where o ← (rβ         i)]
           [`(,i   →η ,o  ) #:where o ← (rη         i)])

  [`(,M →β ,M′)
   ------------
   `(,M →n̅ ,M′)]

  [`(,M →η ,M′)
   ------------
   `(,M →n̅ ,M′)]

  [#:when (∅? (η `(λ ,X ,M)))
   `(,M →n̅ ,M′)
   -------------------------------
   `((λ ,X ,M) →n̅ (λ ,X ,M′))     ]

  [#:when (∅? (β `(,M₁ ,M₂)))
   `(,M₁ →n̅ ,M₁′)
   -------------------------------
   `((,M₁ ,M₂) →n̅ (,M₁′ ,M₂))     ]

  [#:when (∅? (β `(,M₁ ,M₂)))
   #:when (∅? (-->n̅ M₁))
   `(,M₂ →n̅ ,M₂′)
   -------------------------------
   `((,M₁ ,M₂) →n̅ (,M₁ ,M₂′))     ])

;; M → 𝒫(M)
(define -->n̅ (call-with-values (λ () (-->n̅-rules)) compose1))
(define -->>n̅ (compose1 car (repeated -->n̅)))

(module+ test
  (check-equal? (-->>n̅ `((λ y (λ z z)) ,Ω)) (set '(λ z z))))

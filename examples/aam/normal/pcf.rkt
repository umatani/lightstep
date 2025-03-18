#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/inference
         (only-in racket/list split-at)
         (only-in racket/sequence sequence-map)
         (only-in racket/match define-match-expander))
(provide PCF δ)

(module+ test (require rackunit))

;;=============================================================================
;; 3 PCF

(define-language PCF
  [M   ∷= N O X L
          `(μ [,X : ,T] ,L)
          `(,M₀ ,M₁ ...)
          `(if0 ,M₁ ,M₂ ,M₃)]
  [X   ∷= (? symbol? (not 'μ ': 'if0 'λ 'num '→ 'add1 'sub1 '+ '*))]
  [L   ∷= `(λ ([,X : ,T] ...) ,M)]
  [V   ∷= N O L]
  [N   ∷= (? number?)]
  [O   ∷= (? Op₁?) (? Op₂?)]
  [Op₁ ∷= 'add1 'sub1]
  [Op₂ ∷= '+ '*]
  [T   ∷= 'num `(,T₁ ... → ,T)]

  [redex ∷=
         `(μ [,X : ,T] ,L)
         `((λ ([,X : ,T] ...) ,M) ,M′ ...)
         `(,O ,N ...)
         `(if0 ,N ,M₁ ,M₂)])

(module+ test
  (provide fact-5)

  (define fact-5
    '((μ [fact : (num → num)]
         (λ ([n : num])
           (if0 n
                1
                (* n (fact (sub1 n))))))
      5))

  (check-true (M? fact-5)))

;;-----------------------------------------------------------------------------
;; 3.2 The calculus of PCF

;; M → N
(define/match (δ m)
  [`(+ ,N₀ ,N₁) (+ N₀ N₁)]
  [`(* ,N₀ ,N₁) (* N₀ N₁)]
  [`(sub1 ,N) (sub1 N)]
  [`(add1 ,N) (add1 N)])

;; M → 𝒫(X)
(define/match (FV M)
  [N ∅]
  [O ∅]
  [X (set X)]
  [`(λ ([,X : ,T] ...) ,M)
   (set-subtract (FV M) (set←list X))]
  [`(μ [,X : ,T] ,L)
   (set-remove (FV L) X)]
  [`(,M₁ ,M₂ ...)
   (apply ∪ (FV M₁) (map FV M₂))]
  [`(if0 ,M₁ ,M₂ ,M₃)
   (∪ (FV M₁) (FV M₂) (FV M₃))])

;; List([X X]) M → M
(define (subst-vars bs m)
  (match* (bs m)
    [(`([,X₁ ,X₂]) X)
     #:when (eq? X₁ X)
     X₂]
    [(`([,X₁ ,X₂]) `(,any ...))
     (map (λ (m) (subst-vars `([,X₁ ,X₂]) m)) any)]
    [(`([,X₁ ,X₂]) any)
     any]
    [(`([,X₁ ,X₂] ,b ...) M)
     (subst-vars `([,X₁ ,X₂]) (subst-vars b M))]
    [('() any) any]))

;; X M M → M 
(define (subst₁ x₁ m₁ m)
  (match* (x₁ m₁ m)
    ; 1. X₁ bound, so don't continue in λ body
    [(X₁ _ `(λ ,(and bs `([,X : ,T] ...)) ,M))
     #:when (member X₁ X)
     `(λ ,bs ,M)]
    ; or μ
    [(X₁ _ `(μ [,X : ,T] ,M))
     #:when (eq? X₁ X)
     `(μ [,X : ,T] ,M)]
    ; 2. general purpose capture avoiding case
    [(X₁ M₁ `(λ ([,X : ,T] ...) ,M))
     #:do [(define X′ (map (symbol-not-in (set X₁) (FV M₁)) X))]
     `(λ ,(map (λ (x t) `[,x : ,t]) X′ T)
        ,(subst₁ X₁ M₁ (subst-vars (map list X X′) M)))]
    ; and μ
    [(X₁ M₁ `(μ [,X : ,T] ,M))
     #:do [(define X′ ((symbol-not-in (set X₁) (FV M₁)) X))]
     `(μ [,X′ : ,T] ,(subst₁ X₁ M₁ (subst-vars `([,X ,X′]) M)))]
    ; 3. replace X₁ with M₁
    [(X₁ M₁ X)
     #:when (eq? X₁ X)
     M₁]
    ; 4. X₁ and X are different, so don't replace
    [(_ _ X)
     X]
    ; the last cases cover all other expressions  
    [(X₁ M₁ `(,any ...))
     (map (λ (x) (subst₁ X₁ M₁ x)) any)]
    [(_ _ any)
     any]))

;; List([X M]) M → M
(define (subst bs m)
  (match* (bs m)
    [(`([,X₁ ,M₁] ,b ...) M)
     (subst₁ X₁ M₁ (subst b M))]
    [('() M) M]))

(module+ test
  (check-equal? (subst '([x 5] [y 7])
                       '(+ x y))
                '(+ 5 7))
  (check-equal? (subst '([x 5] [y 7])
                       '(if0 0 x y))
                '(if0 0 5 7))

  (check-equal? (subst '([x 5] [y 7])
                       '(μ [a : (num → num)] (λ ([b : num]) (+ x y))))
                '(μ [a : (num → num)] (λ ([b : num]) (+ 5 7))))
  (check-equal? (subst '([x 5] [y 7])
                       '(μ [x : (num → num)] (λ ([y : num]) (+ x y))))
                '(μ [x : (num → num)] (λ ([y : num]) (+ x y)))))

;; M --> M
(define-inference (r-rule)
  [---------------------------------------- "μ"
   `((μ [,X : ,T] ,M)
     → ,(subst `([,X (μ [,X : ,T] ,M)]) M))    ]

  [--------------------------------------- "β"
   `(((λ ([,X : ,T] ...) ,M₀) ,M ...)
     → ,(subst (map list X M) M₀))            ]

  [N₁ ≔ (δ `(,O ,@N₀))
   --------------------- "δ"
   `((,O ,N₀ ...) → ,N₁)    ]

  [------------------------ "if-t"
   `((if0 0 ,M₁ ,M₂) → ,M₁)       ]

  [#:when (not (zero? N))
   ------------------------- "if-f"
   `((if0 ,N ,M₁ ,M₂) → ,M₂)       ])

;; M → 𝒫(M)
(define r (call-with-values (λ () (r-rule)) compose1))

(module+ test
  (check-equal? (r '(add1 5)) (set 6))
  (check-equal? (r '((λ ([x : num]) x) (add1 5))) (set '(add1 5)))
  (check-equal? (r '(sub1 ((λ ([x : num]) x) (add1 5)))) ∅)

  (check-equal? (car ((repeated r) '(add1 5)))
                (set 6))
  (check-equal? (car ((repeated r) '((λ ([x : num]) x) (add1 5))))
                (set 6))
  (check-equal? (car ((repeated r) '(sub1 ((λ ([x : num]) x) (add1 5)))))
                (set '(sub1 ((λ ([x : num]) x) (add1 5))))))

;; TODO: extend cxt pattern to support non-deterministic compatible-closure
;; M --> M
(define-inference (-->ᵣ-rules) #:super [(r-rule)]
  #:do [(define (split-app-cxt Ms)
          (define ((make-cxt i) M)
            (define-values (l r) (split-at Ms i))
            `(,@l ,M ,@(cdr r)))
          (sequence-map (match-λ [(list M i) (values (make-cxt i) M)])
                        (in-values-sequence (in-indexed Ms))))]

  [`(,M → ,M′)
   -------------------------------------------------- "λ-cxt"
   `((λ ,(and bs `([,X : ,T] ...)) ,M) → (λ ,bs ,M′))        ]

  [`(,L → ,L′)
   --------------------------------------- "μ-cxt"
   `((μ [,X : ,T] ,L) → (μ [,X : ,T] ,L′))        ]

  [M′ ← (for/m+ ([(cxt M₁) (split-app-cxt M)])
          (do M₁′ ← (-->ᵣ-rules M₁)
              (return (cxt M₁′))))
   ------------------------------------------- "app-cxt"
   `((,M ...) → ,M′)                                    ]

  [M′ ← (for/m+ ([(cxt M) (split-app-cxt `(,M₁ ,M₂ ,M₃))])
          (do M′ ← (-->ᵣ-rules M)
              (return `(if0 ,@(cxt M′)))))
   ------------------------------------------------------- "if-cxt"
   `((if0 ,M₁ ,M₂ ,M₃) → ,M′)                                      ])

;; M → 𝒫(M)
(define -->ᵣ (call-with-values (λ () (-->ᵣ-rules)) compose1))

(module+ test
  (check-equal? (car ((repeated -->ᵣ) '((λ ([x : num]) x) (add1 5))))
                (set 6))
  (check-equal? (car ((repeated -->ᵣ) '(sub1 ((λ ([x : num]) x) (add1 5)))))
                (set 5))

  (check-equal? (-->ᵣ '((λ ([x : num]) x) (add1 5)))
                (set '((λ ([x : num]) x) 6)
                     '(add1 5)))
  (check-equal?
   (-->ᵣ '(μ [x : num]
                 (λ () (if0 (- x (sub1 2))
                            (+ (add1 5) x)
                            (* x (+ 4 5))))))
   (set '(μ [x : num] (λ () (if0 (- x (sub1 2)) (+ (add1 5) x) (* x 9))))
        '(μ [x : num] (λ () (if0 (- x (sub1 2)) (+ 6 x) (* x (+ 4 5)))))
        '(μ [x : num] (λ () (if0 (- x 1) (+ (add1 5) x) (* x (+ 4 5)))))
        '(λ () (if0 (- (μ [x : num]
                          (λ ()
                            (if0 (- x (sub1 2))
                                 (+ (add1 5) x)
                                 (* x (+ 4 5)))))
                       (sub1 2))
                    (+ (add1 5)
                       (μ [x : num]
                          (λ () (if0 (- x (sub1 2))
                                     (+ (add1 5) x)
                                     (* x (+ 4 5))))))
                    (* (μ [x : num]
                          (λ () (if0 (- x (sub1 2))
                                     (+ (add1 5) x)
                                     (* x (+ 4 5)))))
                       (+ 4 5))))))
  ;; does not terminate
  ;; ((repeated -->ᵣ) '(μ [x : num]
  ;;                      (λ () (if0 (- x (sub1 2))
  ;;                                 (+ (add1 5) x)
  ;;                                 (* x (+ 4 5))))))

  ;; does not terminate
  ;; ((repeated -->ᵣ) fact-5)
  )

;;-----------------------------------------------------------------------------
;; 3.3 Call-by-value and call-by-name: Strategies, contexts, and axioms

(define-match-expander Eₙ
  (syntax-parser
    [(Eₙ p)
     #'(... (cxt Eₙ [□ (and p (? redex?))]
                 `(,□ ,M ...)
                 `(,O ,V ... ,□ ,M ...)
                 `(if0 ,□ ,M₁ ,M₂)))]))

;; M --> M
(define-inference (-->ₙ-rule)
  #:do [(define rr (reducer-of (r-rule)))]
  #:forms (.... [`(,i →r ,o) #:where o ← (rr i)])

  [`(,M →r ,M′)
   --------------------- "Eₙ"
   `(,(Eₙ M) → ,(Eₙ M′))     ])

;; M → 𝒫(M)
(define -->ₙ (call-with-values (λ () (-->ₙ-rule)) compose1))

(module+ test
  ;; (match '(add1 5)
  ;;   [(Eₙ M)
  ;;    (Eₙ M)])

  ;; (match '(* 5 2)
  ;;   [(Eₙ M)
  ;;    (Eₙ M)])

  ;; (match '(if0 5 8 9)
  ;;   [(Eₙ M)
  ;;    (Eₙ M)])

  (check-equal? (-->ₙ '((λ ([x : num]) x) (add1 5))) (set '(add1 5)))
  (check-equal? (car ((repeated -->ₙ) '((λ ([x : num]) x) (add1 5))))
                (set 6))
  (check-equal? (car ((repeated -->ₙ) fact-5)) (set 120)))

(module+ test
  ;; (check-true (reachable? -->ₙ fact-5 120))

  ;; TODO: Too slow
  ;; (define fact-2
  ;;   '((μ [fact : (num → num)]
  ;;        (λ ([n : num])
  ;;          (if0 n
  ;;               1
  ;;               (* n (fact (sub1 n))))))
  ;;     2))
  ;; (reachable? -->ᵣ fact-5 120)
  )

(define-match-expander Eᵥ
  (syntax-parser
    [(Eᵥ p)
     #'(... (cxt Eᵥ [□ (and p (? redex?))]
                 `(,V ... ,□ ,M ...)
                 `(if0 ,□ ,M₁ ,M₂)))]))

;; M --> M
(define-inference (-->ᵥ-rule)
  #:do [(define-inference (v-rule) #:super [(r-rule)]
          [---------------------------------- "β"
           `(((λ ([,X : ,T] ...) ,M₀) ,V ...)
             → ,(subst (map list X V) M₀))       ])
        (define rv (reducer-of (v-rule)))]
  #:forms (.... [`(,i →v ,o) #:where o ← (rv i)])

  [`(,M →v ,M′)
   --------------------- "Eᵥ"
   `(,(Eᵥ M) → ,(Eᵥ M′))     ])

;; M → 𝒫(M)
(define -->ᵥ (call-with-values (λ () (-->ᵥ-rule)) compose1))

(module+ test
  (check-equal? (-->ᵥ '((λ ([x : num]) x) (add1 5)))
                (set '((λ ([x : num]) x) 6)))
  (check-equal? (car ((repeated -->ᵥ) '((λ ([x : num]) x) (add1 5))))
                (set 6))
  (check-equal? (car ((repeated -->ᵥ) fact-5)) (set 120))

  (define Ω
    '((μ [loop : (num → num)]
         (λ ([x : num])
           (loop x)))
      0))
  (check-equal? (car ((repeated -->ₙ) `((λ ([x : num]) 0) ,Ω))) (set 0))
  (check-equal? (car ((repeated -->ᵥ) `((λ ([x : num]) 0) ,Ω))) ∅))

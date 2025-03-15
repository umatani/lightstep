#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax
         (only-in lightstep/monad mapM)
         (only-in racket/list split-at)
         (only-in racket/sequence sequence-map)
         (only-in racket/match match-define define-match-expander)
         (only-in "common.rkt" mmap mmap-lookup mmap-ext reachable?))
(provide PCF δ)

(module+ test (require rackunit))

;;=============================================================================
;; 3 PCF

(define-language PCF
  [M   ∷= N O X L
          `(μ [,X : ,T] ,L)
          `(,M₁ ,M₂ ...)
          `(if0 ,M₁ ,M₂ ,M₃)]
  [X   ∷= (? symbol? (not 'μ ': 'if0 'λ 'num '→))]
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
;; 3.1 Typing judgement

(define/match (Γ bs)
  [`([,X ,T] ...)
   (apply mmap (map list X T))])

(define (Γ? Γ)
  (and (map? Γ)
       (for/and ([x  (dom Γ)]) (X? x))
       (for/and ([ts (rng Γ)]) (for/and ([t (in-set ts)]) (T? t)))))


(define-reduction (⊢)
  [`(,Γ ,X)
   T ← (for/monad+ ([T (in-set (mmap-lookup Γ X))])
         (return T))
   T
   "var"]

  [`(,Γ ,N)
   'num
   "num"]

  [`(,Γ ,(? Op₁?))
   '(num → num)
   "op1"]

  [`(,Γ ,(? Op₂?))
   '(num num → num)
   "op2"]

  [`(,Γ (if0 ,M₁ ,M₂ ,M₃))
   'num ← (⊢ `(,Γ ,M₁))
   T₂ ← (⊢ `(,Γ ,M₂))
   T₃ ← (⊢ `(,Γ ,M₃))
   #:when (equal? T₂ T₃)
   T₂
   "if0"]

  [`(,Γ (μ [,X : ,T] ,L))
   T ← (⊢ `(,(mmap-ext Γ `[,X ,T]) ,L))
   T
   "μ"]

  [`(,Γ (,M₀ ,M₁ ...))
   `(,T₁  ... → ,T) ← (⊢ `(,Γ ,M₀))
   `(,T₁′ ...)      ← (mapM (λ (m) (⊢ `(,Γ ,m))) M₁)
   #:when (andmap equal? T₁ T₁′)
   T
   "app"]

  [`(,Γ (λ ([,X : ,T] ...) ,M))
   #:when (unique X)
   Tₙ ← (⊢ `(,(apply mmap-ext Γ (map list X T)) ,M))
   `(,@T → ,Tₙ)
   "λ"])

(define run-⊢ (letrec-values ([(mrun reducer) (⊢)])
                (compose1 mrun reducer)))

(define (⊢? ΓM T)
  (match (run-⊢ ΓM)
    [(set T′) (equal? T T′)]
    [∅ (error '⊢? "~s cannot be typed" (cadr ΓM))]
    [_ (error '⊢? "derived multiple types for ~s" (cadr ΓM))]))

(module+ test
  (check-true   (⊢? `(,(Γ '()) (λ ([x : num]) x)) '(num → num)))
  (check-equal? (run-⊢ `(,(Γ '()) 3)) (set 'num))
  (check-equal? (run-⊢ `(,(Γ '()) (λ ([x : num]) x))) (set '(num → num)))
  (check-equal? (run-⊢ `(,(Γ '()) (λ ([x : num]) (add1 x)))) (set '(num → num)))
  (check-equal? (run-⊢ `(,(Γ '())
                         (λ ([x : num] [y : num])
                           (+ x y)))) (set '(num num → num)))
  (check-equal? (run-⊢ `(,(Γ '())
                         (λ ([f : (num → num)] [x : num])
                           (f x)))) (set '((num → num) num → num)))

  (check-equal? (run-⊢ `(,(Γ '())
                         (λ ([f : (num num → num)] [x : (num → num)] [y : num])
                           (f x y)))) ∅)

  (check-equal? (run-⊢ `(,(Γ '())
                         (λ ([f : (→ num)])
                           (f)))) (set '((→ num) → num)))
  (check-equal? (run-⊢ `(,(Γ '()) ,fact-5)) (set 'num))

  (check-equal? (run-⊢ `(,(Γ '()) (λ ([x : num] [x : num]) x)))
                (set)))

;;-----------------------------------------------------------------------------
;; 3.2 The calculus of PCF

(define/match (δ M)
  [`(+ ,N₀ ,N₁) (+ N₀ N₁)]
  [`(* ,N₀ ,N₁) (* N₀ N₁)]
  [`(sub1 ,N) (sub1 N)]
  [`(add1 ,N) (add1 N)])

(define/match (FV M)
  [N ∅]
  [O ∅]
  [X (set X)]
  [`(λ ([,X : ,T] ...) ,M)
   (set-subtract (FV M) (list→set X))]
  [`(μ [,X : ,T] ,L)
   (set-remove (FV L) X)]
  [`(,M₁ ,M₂ ...)
   (apply ∪ (FV M₁) (map FV M₂))]
  [`(if0 ,M₁ ,M₂ ,M₃)
   (∪ (FV M₁) (FV M₂) (FV M₃))])

(define ((subst-vars . bs) M)
  (match* (bs M)
    [(`([,X₁ ,M₁]) X₂)
     #:when (equal? X₁ X₂)
     M₁]
    [(`([,X₁ ,M₁]) `(,M₂ ...))
     (map (subst-vars `[,X₁ ,M₁]) M₂)]
    [(`([,X₁ ,M₁]) M₂)
     M₂]
    [(`([,X₁ ,M₁] [,X₂ ,M₂] ...) M₃)
     ((subst-vars `[,X₁ ,M₁]) ((apply subst-vars (map list X₂ M₂)) M₃))]
    [('() M) M]))

(define ((subst₁ X₁ M₁) M₂)
  (match* (X₁ M₁ M₂)
    ; 1. X₁ bound, so don't continue in λ body
    [(X? _ `(λ ([,X₂ : ,T₂] ...) ,M₂))
     #:when (member X₁ X₂)
     `(λ ,(map (λ (X T) `[,X : ,T]) X₂ T₂) ,M₂)]
    ; or μ
    [(X _ `(μ [,X₂ : ,T] ,M₂))
     #:when (equal? X₁ X₂)
     `(μ [,X₂ : ,T] ,M₂)]
    ; 2. general purpose capture avoiding case
    [(X _ `(λ ([,X₂ : ,T₂] ...) ,M₂))
     #:do [(define X₂′ (map (symbol-not-in (set X₁) (FV M₁)) X₂))]
     `(λ ,(map (λ (X T) `[,X : ,T]) X₂′ T₂)
        ,((subst₁ X₁ M₁)
          ((apply subst-vars (map list X₂ X₂′)) M₂)))]
    ; and μ
    [(X _ `(μ [,X₂ : ,T] ,M₂))
     #:do [(define X₂′ ((symbol-not-in (set X₁) (FV M₁)) X₂))]
     `(μ [,X₂′ : ,T] ,((subst₁ X₁ M₁)
                       ((subst-vars `[,X₂ ,X₂′]) M₂)))]
    ; 3. replace X₁ with M₁
    [(X _ X₂)
     #:when (equal? X₁ X₂)
     M₁]
    ; 4. X₁ and X₂ are different, so don't replace
    [(X _ X₂)
     X₂]
    ; the last cases cover all other expressions  
    [(X _ `(,m₂ ...))
     (map (subst₁ X₁ M₁) m₂)]
    [(X _ m₂)
     m₂]))

(define ((subst . bs) M)
  (match* (bs M)
    [(`([,X₁ ,M₁] ,b₂ ...) _)
     ((subst₁ X₁ M₁) ((apply subst b₂) M))]
    [('() _) M]))

(module+ test
  (check-equal? ((subst '[x 5] '[y 7]) '(+ x y)) '(+ 5 7))
  (check-equal? ((subst '[x 5] '[y 7]) '(if0 0 x y)) '(if0 0 5 7))

  (check-equal? ((subst '[x 5] '[y 7])
                 '(μ [a : (num → num)] (λ ([b : num]) (+ x y))))
                 '(μ [a : (num → num)] (λ ([b : num]) (+ 5 7))))
  (check-equal? ((subst '[x 5] '[y 7])
                 '(μ [x : (num → num)] (λ ([y : num]) (+ x y))))
                 '(μ [x : (num → num)] (λ ([y : num]) (+ x y)))))


(define-reduction (r)
  [`(μ [,X : ,T] ,L)
   ((subst `[,X (μ [,X : ,T] ,L)]) L)
   "μ"]

  [`((λ ([,X : ,T] ...) ,M₀) ,M ...)
   ((apply subst (map list X M)) M₀)
   "β"]

  [`(,O ,N₀ ...)
   N₁ ≔ (δ `(,O ,@N₀))
   N₁
   "δ"]

  [`(if0 0 ,M₁ ,M₂)
   M₁
   "if-t"]

  [`(if0 ,N ,M₁ ,M₂)
   #:when (not (zero? N))
   M₂
   "if-f"])

(define step-r (call-with-values (λ () (r)) compose1))

(module+ test
  (check-equal? (step-r '(add1 5)) (set 6))
  (check-equal? (step-r '((λ ([x : num]) x) (add1 5))) (set '(add1 5)))
  (check-equal? (step-r '(sub1 ((λ ([x : num]) x) (add1 5)))) ∅)

  (check-equal? (car ((repeated step-r) '(add1 5)))
                (set 6))
  (check-equal? (car ((repeated step-r) '((λ ([x : num]) x) (add1 5))))
                (set 6))
  (check-equal? (car ((repeated step-r) '(sub1 ((λ ([x : num]) x) (add1 5)))))
                (set '(sub1 ((λ ([x : num]) x) (add1 5))))))

;; TODO: extend cxt pattern to support non-deterministic compatible-closure
(define-reduction (-->ᵣ) #:super [(r)]
  #:do [(define (split-app-cxt Ms)
          (define ((make-cxt i) M)
            (define-values (l r) (split-at Ms i))
            `(,@l ,M ,@(cdr r)))
          (sequence-map (match-λ [(cons i M) (values (make-cxt i) M)])
                        (map cons (build-list (length Ms) (λ (x) x)) Ms)))]

  [`(λ ([,X : ,T] ...) ,M)
   M′ ← (-->ᵣ M)
   `(λ ,(map (λ (X T) `[,X : ,T]) X T) ,M′)
   "λ-cxt"]

  [`(μ [,X : ,T] ,L)
   L′ ← (-->ᵣ L)
   `(μ [,X : ,T] ,L′)
   "μ-cxt"]

  [`(,M ...)
   M′ ← (for/monad+ ([(cxt M₁) (split-app-cxt M)])
          (do M₁′ ← (-->ᵣ M₁)
              (return (cxt M₁′))))
   M′
   "app-cxt"]

  [`(if0 ,M₁ ,M₂ ,M₃)
   M′ ← (for/monad+ ([(cxt M) (split-app-cxt `(,M₁ ,M₂ ,M₃))])
          (do M′ ← (-->ᵣ M)
              (return `(if0 ,@(cxt M′)))))
   M′
   "if-cxt"])

(define step-->ᵣ (letrec-values ([(mrun reducer) (-->ᵣ)])
                   (compose1 mrun reducer)))

(module+ test
  (check-equal? (car ((repeated step-->ᵣ) '((λ ([x : num]) x) (add1 5))))
                (set 6))
  (check-equal? (car ((repeated step-->ᵣ) '(sub1 ((λ ([x : num]) x) (add1 5)))))
                (set 5))

  (check-equal? (step-->ᵣ '((λ ([x : num]) x) (add1 5)))
                (set '((λ ([x : num]) x) 6)
                     '(add1 5)))
  (check-equal?
   (step-->ᵣ '(μ [x : num]
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
    [(Eₙ □:id)
     #'(... (cxt Eₙ [□ (and □ (? redex?))]
                 `(,□ ,M ...)
                 `(,O ,V ... ,□ ,M ...)
                 `(if0 ,□ ,M₁ ,M₂)))]))

(define-reduction (-->ₙ)
  #:do [(define →r (reducer-of (r)))]
  [(Eₙ m)
   M′ ← (→r m)
   (Eₙ M′)
   "Eₙ"])

(define step-->ₙ (call-with-values (λ () (-->ₙ)) compose1))

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

  (check-equal? (step-->ₙ '((λ ([x : num]) x) (add1 5))) (set '(add1 5)))
  (check-equal? (car ((repeated step-->ₙ) '((λ ([x : num]) x) (add1 5))))
                (set 6))
  (check-equal? (car ((repeated step-->ₙ) fact-5)) (set 120)))

(module+ test
  (check-true (reachable? step-->ₙ fact-5 120))

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
    [(Eᵥ □:id)
     #'(... (cxt Eᵥ [□ (and □ (? redex?))]
                 `(,V ... ,□ ,M ...)
                 `(if0 ,□ ,M₁ ,M₂)))]))

(define-reduction (-->ᵥ)
  #:do [(define-reduction (v) #:super [(r)]
          [`((λ ([,X : ,T] ...) ,M₀) ,V ...)
           ((apply subst (map list X V)) M₀)
           "β"])
        (define →v (reducer-of (v)))]
  [(Eᵥ m)
   M′ ← (→v m)
   (Eᵥ M′)
   "Eᵥ"])

(define step-->ᵥ (call-with-values (λ () (-->ᵥ)) compose1))

(module+ test
  (check-equal? (step-->ᵥ '((λ ([x : num]) x) (add1 5)))
                (set '((λ ([x : num]) x) 6)))
  (check-equal? (car ((repeated step-->ᵥ) '((λ ([x : num]) x) (add1 5))))
                (set 6))
  (check-equal? (car ((repeated step-->ᵥ) fact-5)) (set 120))

  (define Ω
    '((μ [loop : (num → num)]
         (λ ([x : num])
           (loop x)))
      0))
  (check-equal? (car ((repeated step-->ₙ) `((λ ([x : num]) 0) ,Ω))) (set 0))
  (check-equal? (car ((repeated step-->ᵥ) `((λ ([x : num]) 0) ,Ω))) ∅))

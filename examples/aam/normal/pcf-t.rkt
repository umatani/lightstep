#lang racket/base
(require lightstep/base lightstep/syntax lightstep/inference
         (only-in "pcf.rkt" PCF))

(module+ test (require rackunit))

;;-----------------------------------------------------------------------------
;; 3.1 Typing judgement

(define-language PCFT #:super PCF
  [Γ ∷= (? map? X→T)])

;; Γ ⊢ M : T
(define-inference (⊢rules)
  #:do [(define (ext Γ xs ts)
          (foldr (λ (x t Γ) (Γ x t)) Γ xs ts))]

  #:forms ([`(,Γ:i ⊢ ,M:i : ,T:o) #:where T ← (⊢rules `(,Γ ,M))])

  [T ≔ (Γ X)
   --------------- "var"
   `(,Γ ⊢ ,X : ,T)      ]

  [---------------- "num"
   `(,Γ ⊢ ,N : num)      ]

  [------------------------------- "op1"
   `(,Γ ⊢ ,(? Op₁?) : (num → num))      ]

  [----------------------------------- "op2"
   `(,Γ ⊢ ,(? Op₂?) : (num num → num))      ]

  [`(,Γ ⊢ ,M₁ : num)
   `(,Γ ⊢ ,M₂ : ,T)
   `(,Γ ⊢ ,M₃ : ,(== T))
   ------------------------------ "if0"
   `(,Γ ⊢ (if0 ,M₁ ,M₂ ,M₃) : ,T)      ]

  [`(,(Γ X T) ⊢ ,L : ,(== T))
   ----------------------------- "μ"
   `(,Γ ⊢ (μ [,X : ,T] ,L) : ,T)    ]

  [`(,Γ ⊢ ,M₀ : (,T₁ ... → ,T))
   `(,T₁′ ...) ← (mapM (λ (m) (⊢ `(,Γ ,m))) M₁)
   #:when (andmap equal? T₁ T₁′)
   -------------------------------------------- "app"
   `(,Γ ⊢ (,M₀ ,M₁ ...) : ,T)                        ]

  [#:when (unique X)
   `(,(ext Γ X T) ⊢ ,M : ,Tₙ)
   -------------------------------------------- "λ"
   `(,Γ ⊢ (λ ([,X : ,T] ...) ,M) : (,@T → ,Tₙ))    ])

;; (Γ M) → 𝒫(T)
(define ⊢ (call-with-values (λ () (⊢rules)) compose1))

;; M T → Boolean
(define (⊢? M T)
  (match (⊢ `(,(↦) ,M))
    [(set T′) (equal? T T′)]
    [∅ (error '⊢? "~s cannot be typed" (cadr M))]
    [_ (error '⊢? "derived multiple types for ~s" (cadr M))]))


(module+ test
  (require (only-in (submod "pcf.rkt" test) fact-5))

  (check-true (⊢? '(λ ([x : num]) x) '(num → num)))
  (check-true (⊢? '3 'num))
  (check-true (⊢? '(λ ([x : num]) x) '(num → num)))
  (check-true (⊢? '(λ ([x : num]) (add1 x)) '(num → num)))
  (check-true (⊢? '(λ ([x : num] [y : num]) (+ x y)) '(num num → num)))
  (check-true (⊢? '(λ ([f : (num → num)] [x : num]) (f x))
                  '((num → num) num → num)))

  (check-exn #rx"cannot be typed"
             (λ () (⊢? '(λ ([f : (num num → num)] [x : (num → num)] [y : num])
                          (f x y))
                       'num)))

  (check-true (⊢? '(λ ([f : (→ num)]) (f)) '((→ num) → num)))
  (check-true (⊢? fact-5 'num))

  (check-exn #rx"cannot be typed"
             (λ () (⊢? '(λ ([x : num] [x : num]) x) 'num))))

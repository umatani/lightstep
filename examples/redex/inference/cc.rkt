#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/transformers
         lightstep/inference
         (only-in racket/match define-match-expander)
         (only-in "iswim.rkt" [ISWIM orig-ISWIM] FV subst δ))
(provide ECxt □ ⊢->cc′ mkCC)

(module+ test (require rackunit))

(define-language ISWIM #:super orig-ISWIM)

;;=============================================================================
;; 6.1 The CC Machine

(define-match-expander ECxt
  (syntax-parser
    [(ECxt p)
     #'(... (cxt ECxt [□ p]
                 `(,V ,□)
                 `(,□ ,M)
                 `(,(? oⁿ?) ,V ... ,□ ,M ...)))]))

(define-match-expander □
  (syntax-parser [(□:id) #'(? (λ (x) (equal? x #()))
                             (app (λ (x) (λ () x)) □))])
  (syntax-parser [(_:id) #'#()]))

(define-inference (⊢->cc)
  [#:when (not (V? M₁))
   ------------------------------------------------------ "cc1"
   `(((,M₁ ,M₂) ,(ECxt (□))) → (,M₁ ,(ECxt `(,(□) ,M₂))))      ]

  [#:when (not (V? M))
   -------------------------------------------------- "cc2"
   `(((,V ,M) ,(ECxt (□))) → (,M ,(ECxt `(,V ,(□)))))      ]

  [#:when (not (V? M₁))
   ------------------------------------------------------ "cc3"
   `(((,(? oⁿ? oⁿ) ,V ... ,M₁ ,M ...) ,(ECxt (□)))
     → (,M₁ ,(ECxt `(,oⁿ ,@V ,(□) ,@M))))                      ]

  [-------------------------------------------------- "ccfiᵥ"
   `((((λ ,X ,M) ,V) ,ECxt) → (,(subst M X V) ,ECxt))        ]

  [---------------------------------------------------------- "ccffi"
   `(((,(? oⁿ? oⁿ) ,(? b? b) ...) ,ECxt) → (,(δ oⁿ b) ,ECxt))        ]

  [---------------------------------------------------- "cc4"
   `((,V ,(ECxt `(,V′ ,(□)))) → ((,V′ ,V) ,(ECxt (□))))      ]

  [-------------------------------------------------- "cc5"
   `((,V ,(ECxt `(,(□) ,M))) → ((,V ,M) ,(ECxt (□))))      ]

  [------------------------------------------------- "cc6"
   `((,V ,(ECxt `(,(? oⁿ? oⁿ) ,V′ ... ,(□) ,M ...)))
     → ((,oⁿ ,@V′ ,V ,@M) ,(ECxt (□))))                   ])


(define-inference (⊢->cc′)
  #:monad (StateT #f (NondetT ID))

  [#:when (not (V? M₁))
   (ECxt (□)) ← get
   (put (ECxt `(,(□) ,M₂)))
   ------------------------ "cc1"
   `((,M₁ ,M₂) → ,M₁)            ]

  [#:when (not (V? M))
   (ECxt (□)) ← get
   (put (ECxt `(,V ,(□))))
   ----------------------- "cc2"
   `((,V ,M) → ,M)              ]

  [#:when (not (V? M₁))
   (ECxt (□)) ← get
   (put (ECxt `(,oⁿ ,@V ,(□) ,@M)))
   ---------------------------------------- "cc3"
   `((,(? oⁿ? oⁿ) ,V ... ,M₁ ,M ...) → ,M₁)      ]

  [---------------------------------- "ccfiᵥ"
   `(((λ ,X ,M) ,V) → ,(subst M X V))        ]

  [------------------------------------------ "ccffi"
   `((,(? oⁿ? oⁿ) ,(? b? b) ...) → ,(δ oⁿ b))        ]

  [(ECxt `(,V′ ,(□))) ← get
   (put (ECxt (□)))
   ------------------------ "cc4"
   `(,V → (,V′ ,V))              ]

  [(ECxt `(,(□) ,M)) ← get
   (put (ECxt (□)))
   ----------------------- "cc5"
   `(,V → (,V ,M))              ]

  [(ECxt `(,(? oⁿ? oⁿ) ,V′ ... ,(□) ,M ...)) ← get
   (put (ECxt (□)))
   ----------------------------------------------- "cc6"
   `(,V → (,oⁿ ,@V′ ,V ,@M))                            ])

(define step⊢->cc (call-with-values (λ () (⊢->cc)) compose1))
(define ⊢->>cc (compose1 car (repeated step⊢->cc)))

(define-match-expander mkCC
  (syntax-parser
    [(_ M ECxt) #'(cons M ECxt)])
  (syntax-parser
    [(_ M ECxt) #'(cons M ECxt)]))

(define step⊢->cc′ (let-values ([(mrun reducer) (⊢->cc′)])
                     (match-λ
                      [(mkCC M ECxt)
                       (mrun ECxt (reducer M))])))
(define ⊢->>cc′ (compose1 car (repeated step⊢->cc′)))

(define/match (evalcc m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>cc `(,M ,(□)))
     [(set `(,(? b? b) ,(□)))
      b]
     [(set `((λ ,X ,(? M? N)) ,(□)))
      'function]
     [x (error 'evalcc "invalid final state: ~a" x)])]
  [_ (error 'evalcc "invalid input: ~a" m)])

(define/match (evalcc′ m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>cc′ (mkCC M (□)))
     [(set (mkCC (? b? b) (□)))
      b]
     [(set (mkCC `(λ ,X ,M) (□)))
      'function]
     [x (error 'evalcc′ "invalid final state: ~a" x)])]
  [_ (error 'evalcc′ "invalid input: ~a" m)])


(module+ test
  (provide Ω)

  (check-equal? (⊢->>cc `((((λ x x) (λ y y)) 1) ,(□)))
                (set `(1 ,(□))))
  (check-equal? (⊢->>cc′ (mkCC '(((λ x x) (λ y y)) 1) (□)))
                (set (cons 1 (□))))
  (check-equal? (⊢->>cc `((+ (add1 2) (* 3 4)) ,(□)))
                (set `(15 ,(□))))
  (check-equal? (⊢->>cc′ (mkCC '(+ (add1 2) (* 3 4)) (□)))
                (set (cons 15 (□))))

  (check-equal? (evalcc '(+ (* 9 (↑ 2 3)) 3)) 75)
  (check-equal? (evalcc '(((λ f (λ x (f x))) (λ y (+ y y))) 8)) 16)
  (check-equal? (evalcc′ '(+ (* 9 (↑ 2 3)) 3)) 75)
  (check-equal? (evalcc′ '(((λ f (λ x (f x))) (λ y (+ y y))) 8)) 16)

  (define Ω '((λ x (x x)) (λ x (x x))))
  (check-equal? (⊢->>cc `(,Ω ,(□))) ∅)
  (check-equal? (⊢->>cc′ (mkCC Ω (□))) ∅))

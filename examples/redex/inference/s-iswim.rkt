#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/inference
         (only-in racket/match define-match-expander)
         (only-in racket/sequence sequence-map)
         (only-in "lam.rkt" [α lam:α])
         (only-in "iswim.rkt" δ δ-rule)
         (only-in "cs.rkt" [S-ISWIM orig-S-ISWIM]
                  [AV orig-AV] [FV orig-FV] [subst orig-subst]))
(provide S-ISWIM FV AV substs subst E s step-s)

(module+ test (require rackunit))

;;=============================================================================
;; 9.3 The State ISWIM Calculus

(define-language S-ISWIM #:super orig-S-ISWIM
  [M ∷= .... `(letrec ,Σ ,M)])

(define/match (FV m) #:super orig-FV
  [`(letrec ,Σ ,M)
   (let ([Xs (dom Σ)]
         [Vs (rng Σ)])
     (set-subtract (apply ∪ (FV M) (set-map FV Vs))
                   Xs))])

(define/match (AV m) #:super orig-AV
  [`(letrec ,Σ ,M)
   (let ([Xs (dom Σ)]
         [Vs (rng Σ)])
     (set-subtract (apply ∪ (AV M) (set-map AV Vs))
                   Xs))])

(define/match (substs m xs ms)
  [(M '() '()) M]
  [(M (cons X Xs) (cons M′ Ms)) (substs (subst M X M′) Xs Ms)])

(define/match (subst m₁ x₂ m₂) #:super orig-subst
  [(`(letrec ,(and Σ (↦ [Xᵢ Vᵢ] ...)) ,M) X₂ M₂)
   (if (map-∈ X₂ Σ)
     `(letrec ,Σ ,M)
     (let* ([rename (symbol-not-in (FV `(letrec ,Σ ,M)) (FV M₂))]
            [Yᵢ (map rename Xᵢ)]
            [Σ′ (for/map ([V Vᵢ] [Y Yᵢ])
                  (values Y (subst (substs V Xᵢ Yᵢ) X₂ M₂)))])
       `(letrec ,Σ′ ,(subst (substs M Xᵢ Yᵢ) X₂ M₂))))])

(module+ test
  (check-equal? (subst `(letrec ,(↦ ['x 1] ['y 2]) (+ x y z)) 'y 100)
                `(letrec ,(↦ ['x 1] ['y 2]) (+ x y z)))
  (check-equal? (subst `(letrec ,(↦ ['x 1] ['y 2]) (+ x y z)) 'z 100)
                `(letrec ,(↦ ['x 1] ['y 2]) (+ x y 100))))


(define-nondet-match-expander Cxt
  (λ (stx)
    (syntax-case stx ()
      [(Cxt □)
       #'(nondet-cxt Cxt □
                     ;`(λ ,X ,(? M? □)) ;; non-termination
                     `(,(? M? □) ,M)
                     `(,V ,(? M? □))
                     `(,(? oⁿ?) ,V (... ...) ,(? M? □) ,M (... ...))
                     `(set ,X ,(? M? □))    ; NEW
                     `(letrec ,Σ ,(? M? □)) ; NEW
                     )])))

(define (split-Σ-cxt Σ)
  (define ((make-cxt x) x′ v)
    ((map-remove Σ x) x′ v))
  (sequence-map (λ (x v) (values (make-cxt x) x v)) (in-map Σ)))

(define-inference (α) #:super [(lam:α)]
  [rename ≔ (apply symbol-not-in (FV M) (set-map FV (dom Σ)))
   (list Xᵢ X′ Σ′) ← (for/monad+ ([(cxt Xᵢ Mᵢ) (split-Σ-cxt Σ)])
                       (do X′ ≔ (rename Xᵢ)
                           (return (list Xᵢ X′ (cxt X′ Mᵢ)))))
   Σ″ ≔ (for/map ([(Xⱼ Vⱼ) (in-map Σ′)])
          (values Xⱼ (subst Vⱼ Xᵢ X′)))
   -------------------------------------------------------------
   `((letrec ,Σ ,M) → (letrec ,Σ″ ,(subst M Xᵢ X′)))            ])

(define step-α (call-with-values (λ () (α)) compose1))

(module+ test
  ;(step-α `(letrec ,(↦ ['x 1] ['y 2]) (+ x y)))
  )

(define-inference (-->α) #:super [(α)]
  [`(,m → ,M′) 
   -----------------------
   `(,(Cxt m) → ,(Cxt M′))])

(define step-->α (call-with-values (λ () (-->α)) compose1))

(module+ test
  ;; (step-->α `(letrec ,(↦ ['x 1] ['y 2])
  ;;              (letrec ,(↦ ['z 3])
  ;;                (+ x y))))
  )

(define-inference (alloc)
  [#:when (∈ X (AV M))
   ------------------------------------------
   `(((λ ,X ,M) ,V) → (letrec ,(↦ [X V]) ,M))])


;; re-interpret M
(define-match-expander E
  (syntax-parser
    [(E p)
     #'(... (cxt E [□ p]
                 `(,V ,□)
                 `(,□ ,M)
                 `(,(? oⁿ?) ,V ... ,□ ,M ...)
                 `(set ,X ,□) ; NEW
                 ))]))

(define-inference (lift)
  [#:when (not (equal? x `(letrec ,Σ ,M)))
   rename ≔ (symbol-not-in (FV (E `(letrec ,Σ ,M))))
   Yᵢ ≔ (map rename Xᵢ)
   Σ′ ≔ (for/map ([V Vᵢ] [Y Yᵢ])
          (values Y (substs V Xᵢ Yᵢ)))
   ----------------------------------------------------
   `(,(and x (E `(letrec ,(and Σ (↦ [Xᵢ Vᵢ] ...)) ,M)))
     → (letrec ,Σ′ ,(E (substs M Xᵢ Yᵢ))))             ])

(define-inference (deref)
  [#:when (map-∈ X Σ)
   ----------------------------------------------
   `((letrec ,Σ ,(E X)) → (letrec ,Σ ,(E (Σ X))))])

(define-inference (assign)
  [#:when (map-∈ X Σ)
   ---------------------------------------------------------------
   `((letrec ,Σ ,(E `(set ,X ,V)))
     → (letrec ,(Σ X V) ,(E (Σ X))))])

(define-inference (merge)
  [rename ≔ (apply symbol-not-in
                   (dom Σ) (FV `(letrec ,Σ′ ,M))
                   (set-map FV (rng Σ)))
   Yᵢ ≔ (map rename Xᵢ)
   Σ″ ≔ (⊔ Σ (for/map ([V Vᵢ] [Y Yᵢ])
               (values Y (substs V Xᵢ Yᵢ))))
   ----------------------------------------------------
   `((letrec ,Σ (letrec ,(and Σ′ (↦ [Xᵢ Vᵢ] ...)) ,M))
     → (letrec ,Σ″ ,(substs M Xᵢ Yᵢ)))                 ])

(define-inference (βv-rule)
  [#:when (not (∈ X (AV M)))
   ----------------------------------
   `(((λ ,X ,M) ,V) → ,(subst M X V))])

(define-inference (s) #:super [(βv-rule) (δ-rule δ)
                                         (alloc)
                                         (deref)
                                         (assign)
                                         (lift)
                                         (merge)])

(define step-s (call-with-values (λ () (s)) compose1))

(define-inference (-->s) #:super [(s)]
  [`(,m → ,M′)
   -----------------------
   `(,(Cxt m) → ,(Cxt M′))])

(define step-->s (call-with-values (λ () (-->s)) compose1))
(define -->>s (compose1 car (repeated step-->s)))

(module+ test
  (check-equal? (-->>s `((λ x (+ 3 (letrec ,(↦ ['y 1])
                                     ((λ z (+ z y))
                                      (set x (+ x 1))))))
                         0) #:limit 10)
                (set `(letrec ,(↦ ['x 1] ['y 1]) 4))))

(define/match (evalₛ m)
  [M
   #:when (∅? (FV M))
   (match (-->>s M)
    [(set (or (? b? b) `(letrec ,(? Σ?) ,(? b? b)))) b]
    [(set (or `(λ ,X ,M) `(letrec ,(? Σ?) (λ ,X ,M)))) 'function]
    [x (error 'evalₛ "invalid answer: ~a" x)])]
  [_ (error 'evalₛ "invalid input: ~a" m)])

(module+ test
  (check-equal? (evalₛ `((λ x (+ 3 (letrec ,(↦ ['y 1])
                                     ((λ z (+ z y))
                                      (set x (+ x 1))))))
                         0))
                4))

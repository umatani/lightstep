#lang racket/base
(require lightstep/base lightstep/syntax lightstep/inference
         (only-in "pcf-sigma.rkt" injσ)
         (only-in "pcf-sigma-o.rkt" -->vσ∘ -->>vσ∘)
         (only-in "pcf-sigma-hat.rkt" [PCFσ^ orig-PCFσ^] -->vσ^ -->>vσ^))

(module+ test (require rackunit))

;;=============================================================================
;; 4.4 Soundness

(define-language PCFσ^ #:super orig-PCFσ^)

(define-inference (⊑σ-rules)
  #:forms ([`(,σ:i ⊑σ ,σ^:i) #:where #t ← (⊑σ-rules `(,σ ,σ^))]
           [`(,V   ⊑V ,V^  ) #:where #t ← (rV       `(,V ,V^))]
           [`(,ς   ⊑ς ,ς^  ) #:where #t ← (rς       `(,ς ,ς^))]
           [`(,Σ   ⊑Σ ,Σ^  ) #:where #t ← (rΣ       `(,Σ ,Σ^))])

  [`(,V ⊑V ,V^)
   ------------
   `(,V ⊑σ ,V^)]

  [`(,ς ⊑ς ,ς^)    `(,Σ ⊑Σ ,Σ^)
   ----------------------------
   `((,ς ,Σ) ⊑σ (,ς^ ,Σ^))     ])

(define-inference (⊑V-rules)
  #:forms ([`(,V:i ⊑V ,V^:i) #:where #t ← (⊑V-rules `(,V ,V^))]
           [`(,ρ   ⊑ρ ,ρ^  ) #:where #t ← (rρ       `(,ρ ,ρ^))])

  [-----------
   `(,N ⊑V num)]

  [-----------
   `(,N ⊑V ,N)]

  [-----------
   `(,O ⊑V ,O)]

  [`(,ρ ⊑ρ ,ρ^)
   ----------------------
   `((,L ,ρ) ⊑V (,L ,ρ^))]
  
  [`(,ρ ⊑ρ ,ρ^)
   --------------------------------------------------
   `(((μ [,X : ,T] ,L) ,ρ) ⊑V ((μ [,X : ,T] ,L) ,ρ^))])


(define-inference (⊑K-rules)
  #:forms ([`(,K:i ⊑K ,K^:i) #:where #t ← (⊑K-rules `(,K ,K^))]
           [`(,F   ⊑F ,F^  ) #:where #t ← (rF       `(,F ,F^))]
           [`(,A   ⊑A ,A^  ) #:where #t ← (rA       `(,A ,A^))])

  [-----------
   `(() ⊑K ())]

  [`(,F ⊑F ,F^)    `(,A ⊑A ,A^)
   ----------------------------
   `((,F ,A) ⊑K (,F^ ,A^))     ])

(define-inference (⊑U-rules)
  #:forms ([`(,U:i ⊑U ,U^:i) #:where #t ← (⊑U-rules `(,U ,U^))]
           [`(,V   ⊑V ,V^  ) #:where #t ← (rV       `(,V ,V^))]
           [`(,K   ⊑K ,K^  ) #:where #t ← (rK       `(,K ,K^))])

  [`(,V ⊑V ,V^)
   ------------
   `(,V ⊑U ,V^)]

  [`(,K ⊑K ,K^)
   ------------
   `(,K ⊑U ,K^)])


(define-inference (⊑A-rules)
  #:forms ([`(,A:i ⊑A ,A^:i) #:where #t ← (⊑A-rules `(,A ,A^))]
           [`(,F   ⊑F ,F^  ) #:where #t ← (rF       `(,F ,F^))])

  [----------------
   `((,X ,_) ⊑A ,X)]

  [`(,F ⊑F ,F^)
   -----------------
   `((,F ,_) ⊑A ,F^)])

(define-inference (⊑F-rules)
  #:forms ([`(,F:i ⊑F ,F^:i) #:where #t ← (⊑F-rules `(,F ,F^))]
           [`(,V   ⊑V ,V^  ) #:where #t ← (rV       `(,V ,V^))]
           [`(,C   ⊑C ,C^  ) #:where #t ← (rC       `(,C ,C^))])

  [`(#t ...) ← (mapM (compose1 rV (zipWith list)) V V^)
   `(#t ...) ← (mapM (compose1 rC (zipWith list)) C C^)
   ----------------------------------------------------
   `((,V ... □ ,C ...) ⊑F (,V^ ... □ ,C^ ...))         ]

  [`(,C₁ ⊑C ,C₁^)        `(,C₂ ⊑C ,C₂^)
   ---------------------------------------
   `((if0 □ ,C₁ ,C₂) ⊑F (if0 □ ,C₁^ ,C₂^))])

(define-inference (⊑ρ-rules)
  #:forms ([`(,ρ:i ⊑ρ ,ρ^:i) #:where #t ← (⊑ρ-rules `(,ρ ,ρ^))]
           [`(,A   ⊑A ,A^  ) #:where #t ← (rA       `(,A ,A^))])

  [------------------
   `(,(↦) ⊑ρ ,(? ρ?))]

  [`(,A ⊑A ,A^)        `(,(map←list b) ⊑ρ ,ρ)
   -----------------------------------------------------
   `(,(↦ [X A] b ...) ⊑ρ ,(and ρ (↦ [(== X) A^] _ ...)))])

(define-inference (⊑C-rules)
  #:forms ([`(,C:i ⊑C ,C^:i) #:where #t ← (⊑C-rules `(,C ,C^))]
           [`(,V   ⊑V ,V^  ) #:where #t ← (rV       `(,V ,V^))]
           [`(,ρ   ⊑ρ ,ρ^  ) #:where #t ← (rρ       `(,ρ ,ρ^))])

  [`(,V ⊑V ,V^)
   -------------
   `(,V ⊑C ,V^)]

  [`(,ρ ⊑ρ ,ρ^)
   -------------------------------------
   `((,M ,(? ρ? ρ)) ⊑C (,M ,(? ρ? ρ^)))])

(define-inference (⊑ς-rules)
  #:forms ([`(,ς:i ⊑ς ,ς^:i) #:where #t ← (⊑ς-rules `(,ς ,ς^))]
           [`(,C   ⊑C ,C^  ) #:where #t ← (rC       `(,C ,C^))]
           [`(,K   ⊑K ,K^  ) #:where #t ← (rK       `(,K ,K^))]
           [`(,V   ⊑V ,V^  ) #:where #t ← (rV       `(,V ,V^))])

  [`(,C ⊑C ,C^)    `(,K ⊑K ,K^)
   ----------------------------
   `((,C ,K) ⊑ς (,C^ ,K^))     ]

  [`(,V ⊑V ,V^)
   ------------
   `(,V ⊑ς ,V^)])

(define-inference (⊑Σ-rules)
  #:forms ([`(,Σ:i ⊑Σ ,Σ^:i) #:where #t ← (⊑Σ-rules `(,Σ ,Σ^))]
           [`(,A   ⊑A ,A^  ) #:where #t ← (rA       `(,A ,A^))]
           [`(,U   ⊑U ,U^  ) #:where #t ← (rU       `(,U ,U^))])

  [#:when (for/and ([(a u) (in-pmap Σ)])
            (for/or ([(a^ u^) (in-pmap Σ^)])
              (and (⊑A? a a^) (⊑U? u u^))))
   -----------------------------------------
   `(,Σ ⊑Σ ,Σ^)                             ])


(define-values (⊑σ rσ) (let-values ([(mrun reducer) (⊑σ-rules)])
                         (values (compose1 mrun reducer) reducer)))
(define-values (⊑V rV) (let-values ([(mrun reducer) (⊑V-rules)])
                         (values (compose1 mrun reducer) reducer)))
(define-values (⊑K rK) (let-values ([(mrun reducer) (⊑K-rules)])
                         (values (compose1 mrun reducer) reducer)))
(define-values (⊑U rU) (let-values ([(mrun reducer) (⊑U-rules)])
                         (values (compose1 mrun reducer) reducer)))
(define-values (⊑A rA) (let-values ([(mrun reducer) (⊑A-rules)])
                         (values (compose1 mrun reducer) reducer)))
(define-values (⊑F rF) (let-values ([(mrun reducer) (⊑F-rules)])
                         (values (compose1 mrun reducer) reducer)))
(define-values (⊑C rC) (let-values ([(mrun reducer) (⊑C-rules)])
                         (values (compose1 mrun reducer) reducer)))
(define-values (⊑ρ rρ) (let-values ([(mrun reducer) (⊑ρ-rules)])
                         (values (compose1 mrun reducer) reducer)))
(define-values (⊑ς rς) (let-values ([(mrun reducer) (⊑ς-rules)])
                         (values (compose1 mrun reducer) reducer)))
(define-values (⊑Σ rΣ) (let-values ([(mrun reducer) (⊑Σ-rules)])
                         (values (compose1 mrun reducer) reducer)))

(define (⊑σ? σ σ^) (match (⊑σ `(,σ ,σ^))
                     [(set #t) #t]
                     [(set)    #f]
                     [_ (error "no such case")]))
(define (⊑V? V V^) (match (⊑V `(,V ,V^))
                     [(set #t) #t]
                     [(set)    #f]
                     [_ (error "no such case")]))
(define (⊑K? K K^) (match (⊑K `(,K ,K^))
                     [(set #t) #t]
                     [(set)    #f]
                     [_ (error "no such case")]))
(define (⊑U? U U^) (match (⊑U `(,U ,U^))
                     [(set #t) #t]
                     [(set)    #f]
                     [_ (error "no such case")]))
(define (⊑A? A A^) (match (⊑A `(,A ,A^))
                     [(set #t) #t]
                     [(set)    #f]
                     [_ (error "no such case")]))
(define (⊑F? F F^) (match (⊑F `(,F ,F^))
                     [(set #t) #t]
                     [(set)    #f]
                     [_ (error "no such case")]))
(define (⊑C? C C^) (match (⊑C `(,C ,C^))
                     [(set #t) #t]
                     [(set)    #f]
                     [_ (error "no such case")]))
(define (⊑ρ? ρ ρ^) (match (⊑ρ `(,ρ ,ρ^))
                     [(set #t) #t]
                     [(set)    #f]
                     [_ (error "no such case")]))
(define (⊑ς? ς ς^) (match (⊑ς `(,ς ,ς^))
                     [(set #t) #t]
                     [(set)    #f]
                     [_ (error "no such case")]))
(define (⊑Σ? Σ Σ^) (match (⊑Σ `(,Σ ,Σ^))
                     [(set #t) #t]
                     [(set)    #f]
                     [_ (error "no such case")]))


(module+ test
  (require (only-in (submod "pcf.rkt" test) FACT fact-5 Ω))

  ;; (-->vσ∘ (injσ fact-5))
  ;; (-->vσ^ (injσ fact-5))

  ;; (-->>vσ∘ (injσ fact-5))
  (set-size (cdr ((repeated -->vσ∘) (injσ (FACT 0)))))
  (set-size (cdr ((repeated -->vσ∘) (injσ (FACT 1)))))
  (set-size (cdr ((repeated -->vσ∘) (injσ (FACT 2)))))
  (set-size (cdr ((repeated -->vσ∘) (injσ (FACT 3)))))
  (set-size (cdr ((repeated -->vσ∘) (injσ (FACT 4)))))
  (set-size (cdr ((repeated -->vσ∘) (injσ (FACT 5)))))
  (set-size (cdr ((repeated -->vσ^) (injσ (FACT 0)))))
  (set-size (cdr ((repeated -->vσ^) (injσ (FACT 1)))))
  (set-size (cdr ((repeated -->vσ^) (injσ (FACT 2)))))
  (set-size (cdr ((repeated -->vσ^) (injσ (FACT 3)))))
  (set-size (cdr ((repeated -->vσ^) (injσ (FACT 4)))))
  (set-size (cdr ((repeated -->vσ^) (injσ (FACT 5)))))
  ;(set-size (cdr ((repeated -->vσ^) (injσ fact-5))))

  (⊑σ? (injσ fact-5) (injσ fact-5))
  )

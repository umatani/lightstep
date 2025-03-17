#lang racket/base
(require lightstep/base lightstep/syntax lightstep/transformers
         (only-in "iswim.rkt" δ)
         (only-in "s-iswim.rkt" FV)
         (only-in "cesk.rkt" [CESK orig-CESK] ⊢->cesk mkCESK))

(module+ test (require rackunit))

;;=============================================================================
;; 9.5 The CESK Machine with GC

(define-language CESK #:super orig-CESK)

;; (∪ (M E) E Σ κ) → 𝒫(σ)
(define/match (LL x)
  [`(,M ,E) (LL E)]
  [E (rng E)]
  [Σ (apply ∪ (set-map LL (rng Σ)))]

  ['mt ∅]
  [`(fn (,V ,E) ,(? κ? κ)) (∪ (LL E) (LL κ))]
  [`(ar (,M ,E) ,(? κ? κ)) (∪ (LL E) (LL κ))]
  [`(op (,c ... ,(? oⁿ? oⁿ)) (,c′ ...) ,(? κ? κ))
   (apply ∪ (LL κ) (map LL `(,@c ,@c′)))]
  [`(set ,(? σ? σ) ,(? κ? κ)) (set-add (LL κ) σ)])

;; (𝒫(σ) 𝒫(σ) Σ) --> (𝒫(σ) 𝒫(σ) Σ)
(define-reduction (⊢->gc)
  [`(,Grey ,Brack ,Σ)
   (set σ₀ σ ...) ≔ Grey
   `(,(set-subtract (∪ Grey (LL (Σ σ₀)))
                    (set-add Brack σ₀))
     ,(set-add Brack σ₀)
     ,Σ)])

;; (𝒫(σ) 𝒫(σ) Σ) → 𝒫((𝒫(σ) 𝒫(σ) Σ))
(define step⊢->gc (call-with-values (λ () (⊢->gc)) compose1))
(define ⊢->>gc (compose1 car (repeated step⊢->gc)))

;; (M E Σ κ) --> (M E Σ κ)
(define-reduction (⊢->gc-in-cesk)
  #:monad (StateT #f (StateT #f (NondetT ID)))
  #:do [(define get-Σ (bind get (compose1 return car)))
        (define get-κ (bind get (compose1 return cdr)))
        (define (put-Σ Σ)
          (do `(,_ . ,κ) ← get
              (put `(,Σ . ,κ))))
        (define (put-κ κ)
          (do `(,Σ . ,_) ← get
              (put `(,Σ . ,κ))))]
  [`(,M ,E)
   Σ ← get-Σ
   κ ← get-κ
   (set `(,∅ ,Live ,_)) ≔ (⊢->>gc `(,(∪ (LL E) (LL κ)) ,∅ ,Σ))
   (put-Σ (restrict Σ Live))
   `(,M ,E)
   "ceskgcI"])

;; (M E Σ κ) → 𝒫((M E Σ κ))
(define step⊢->gc-in-cesk (let-values ([(mrun reducer) (⊢->gc-in-cesk)])
                            (match-λ
                             [(mkCESK M E Σ (? κ? κ))
                              (mrun κ Σ (reducer `(,M ,E)))])))
(define step⊢->cesk (let-values ([(mrun reducer) (⊢->cesk)])
                      (match-λ
                       [(mkCESK M E Σ (? κ? κ))
                        (mrun κ Σ (reducer `(,M ,E)))])))

;; (M E Σ κ) → 𝒫((M E Σ κ))
(define (step⊢->cesk+gc ς)
  (apply ∪ (set-map step⊢->gc-in-cesk #; set ;; to compare with no-gc
                    (step⊢->cesk ς))))
(define ⊢->>cesk+gc (compose1 car (repeated step⊢->cesk+gc)))

;; M → V
(define/match (evalcesk+gc m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>cesk+gc (mkCESK M (↦) (↦) 'mt))
     [(set (mkCESK (? b? b) E Σ 'mt))
      b]
     [(set (mkCESK `(λ ,X ,M) E Σ 'mt))
      'function]
     [x (error 'evalcesk+gc "invalid final state: ~s" x)])]
  [_ (error 'evalcesk+gc "invalid input: ~s" m)])

(module+ test
  (require (only-in "cs.rkt" LET SEQ))

  (check-equal? (⊢->>cesk+gc (mkCESK
                              `((λ x ,(SEQ '(set x (* x x)) '(add1 x))) 8)
                              (↦) (↦) 'mt))
                (set (mkCESK 65 (↦) (↦) 'mt)))
  (check-equal? (⊢->>cesk+gc (mkCESK
                              (LET '([x 0])
                                   (SEQ '(set x 5)
                                        (LET '([x 9]) (SEQ '(set x (+ x x))
                                                           'x))))
                              (↦) (↦) 'mt))
                (set (mkCESK 18 (↦) (↦) 'mt))))

#lang racket/base
(require lightstep/base lightstep/syntax lightstep/transformers
         lightstep/inference
         (only-in "iswim.rkt" δ)
         (only-in "s-iswim.rkt" FV)
         (only-in "cesk.rkt" [CESK orig-CESK] ⊢->cesk-rules mkCESK))

(module+ test (require rackunit))

;;=============================================================================
;; 9.5 The CESK Machine with GC

(define-language CESK #:super orig-CESK)

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

(define-inference (⊢->gc-rules)
  [(set σ₀ σ ...) ≔ Grey
   Grey′ ≔ (set-subtract (∪ Grey (LL (Σ σ₀)))
                         (set-add Brack σ₀))
   Brack′ ≔ (set-add Brack σ₀)
   ------------------------------------------
   `((,Grey ,Brack ,Σ) → (,Grey′ ,Brack′ ,Σ))])

(define ⊢->gc (call-with-values (λ () (⊢->gc-rules)) compose1))
(define ⊢->>gc (compose1 car (repeated ⊢->gc)))

(define-inference (⊢->gc-in-cesk-rules)
  #:monad (StateT #f (StateT #f (StateT #f (NondetT ID))))
  #:do [(define get-E (bind get (compose1 return car)))
        (define get-Σ (bind get (compose1 return cadr)))
        (define get-κ (bind get (compose1 return cddr)))
        (define (put-E E)
          (do `(,_ ,Σ . ,κ) ← get
              (put `(,E ,Σ . ,κ))))
        (define (put-Σ Σ)
          (do `(,E ,_ . ,κ) ← get
              (put `(,E ,Σ . ,κ))))
        (define (put-κ κ)
          (do `(,E ,Σ . ,_) ← get
              (put `(,E ,Σ . ,κ))))]

  [E ← get-E    Σ ← get-Σ    κ ← get-κ
   (set `(,∅ ,Live ,_)) ≔ (⊢->>gc `(,(∪ (LL E) (LL κ)) ,∅ ,Σ))
   (put-Σ (restrict Σ Live))
   ----------------------------------------------------------- "ceskgcI"
   `(,M → ,M)                                                           ])

(define ⊢->gc-in-cesk (let-values ([(mrun reducer) (⊢->gc-in-cesk-rules)])
                        (match-λ
                         [(mkCESK M E Σ (? κ? κ))
                          (mrun κ Σ E (reducer M))])))

(define ⊢->cesk (let-values ([(mrun reducer) (⊢->cesk-rules)])
                  (match-λ
                   [(mkCESK M E Σ (? κ? κ))
                    (mrun κ Σ E (reducer M))])))

(define (⊢->cesk+gc ς)
  (apply ∪ (set-map ⊢->gc-in-cesk #; set ;; to compare with no-gc
                    (⊢->cesk ς))))

(define ⊢->>cesk+gc (compose1 car (repeated ⊢->cesk+gc)))

(define/match (evalcesk+gc m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>cesk+gc (mkCESK M (↦) (↦) 'mt))
     [(set (mkCESK (? b? b) E Σ 'mt))
      b]
     [(set (mkCESK `(λ ,X ,M) E Σ 'mt))
      'function]
     [x (error 'evalcesk+gc "invalid final state: ~a" x)])]
  [_ (error 'evalcesk+gc "invalid input: ~a" m)])

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

#lang racket/base
(require (for-syntax racket/base syntax/parse)
         lightstep/base lightstep/syntax lightstep/transformers
         lightstep/inference
         (only-in "cc.rkt" □)
         (only-in "e-iswim.rkt" δ [δ-rules orig-δ-rules])
         (only-in "h-iswim.rkt"
                  [H-ISWIM orig-H-ISWIM] FV subst FCxt
                  [δerr-rules orig-δerr-rules]))

(module+ test (require rackunit))

;;=============================================================================
;; 8.3 The CHC Machine

(define-language H-ISWIM #:super orig-H-ISWIM
  [H ∷= (? list? λFCxts)])

;; (M H FCxt) --> (M H FCxt)
;; to match the monad
(define-inference (δ-rules) #:super [(orig-δ-rules δ)]
  #:monad (StateT #f (StateT #f (NondetT ID))))

;; (M H FCxt) --> (M H FCxt)
;; to match the monad
(define-inference (δerr-rules) #:super [(orig-δerr-rules δ)]
  #:monad (StateT #f (StateT #f (NondetT ID))))

;; (M H FCxt) --> (M H FCxt)
(define-inference (⊢->chc-rules)
  #:monad (StateT #f (StateT #f (NondetT ID)))
  #:do [(define get-H (bind get (compose1 return car)))
        (define get-C (bind get (compose1 return cdr)))
        (define (put-H h)
          (do (cons _ c) ← get
              (put (cons h c))))
        (define (put-C c)
          (do (cons h _) ← get
              (put (cons h c))))

        (define rδ    (reducer-of (δ-rules)))
        (define rδerr (reducer-of (δerr-rules)))]
  #:forms ([`(,i:i →chc  ,o:o) #:where o ← (⊢->chc-rules i)]
           [`(,i   →δ    ,o  ) #:where o ← (rδ           i)]
           [`(,i   →δerr ,o  ) #:where o ← (rδerr        i)])

  [#:when (not (V? M₁))
   (FCxt (□)) ← get-C
   (put-C (FCxt `(,(□) ,M₂)))
   -------------------------- "chc1"
   `((,M₁ ,M₂) →chc ,M₁)            ]

  [#:when (not (V? M))
   (FCxt (□)) ← get-C
   (put-C (FCxt `(,V ,(□))))
   ------------------------- "chc2"
   `((,V ,M) →chc ,M)              ]

  [#:when (not (V? M))
   (FCxt (□)) ← get-C
   (put-C (FCxt `(,oⁿ ,@V ,(□) ,@M′)))
   ------------------------------------------ "chc3"
   `((,(? oⁿ? oⁿ) ,V ... ,M ,M′ ...) →chc ,M)       ]

  [------------------------------------- "chcfiᵥ"
   `(((λ ,X ,M) ,V) →chc ,(subst M X V))         ]

  [`((,oⁿ ,@b) →δ ,(? b? b′))
   --------------------------------------- "chcffi"
   `((,(? oⁿ? oⁿ) ,(? b? b) ...) →chc ,b′)         ]

  [(FCxt `(,V′ ,(□))) ← get-C
   (put-C (FCxt (□)))
   -------------------------- "chc4"
   `(,V →chc (,V′ ,V))              ]

  [(FCxt `(,(□) ,M)) ← get-C
   (put-C (FCxt (□)))
   ------------------------- "chc5"
   `(,V →chc (,V ,M))              ]

  [(FCxt `(,(? oⁿ? oⁿ) ,V′ ... ,(□) ,M ...)) ← get-C
   (put-C (FCxt (□)))
   ------------------------------------------------- "chc6"
   `(,V →chc (,oⁿ ,@V′ ,V ,@M))                            ]

  [`(,M →δerr (throw ,(? b? b)))
   ------------------------------ "chc7"
   `(,M →chc (throw ,b))                ]

  ['() ← get-H
   f ← get-C
   #:when (not (equal? f (□)))
   (put-C (□))
   ------------------------------------ "chc8"
   `((throw ,(? b? b)) →chc (throw ,b))       ]

  [H ← get-H
   (FCxt (□)) ← get-C
   (put-H (cons `((λ ,X ,M′) ,(FCxt (□))) H))
   (put-C (□))
   ------------------------------------------ "chc9"
   `((catch ,M with (λ ,X ,M′)) →chc ,M)            ]

  [(cons `(,V′ ,(FCxt (□))) H) ← get-H
   f ← get-C
   #:when (equal? f (□))
   (put-H H)
   (put-C (FCxt (□)))
   ----------------------------------- "chc10"
   `(,V →chc ,V)                              ]

  [H ← get-H
   f ← get-C
   #:when (and (not (null? H)) (not (equal? f (□))))
   (put-C (□))
   ------------------------------------------------- "chc11"
   `((throw ,(? b? b)) →chc (throw ,b))                     ]
  
  [(cons `(,V ,(FCxt (□))) H) ← get-H
   f ← get-C
   #:when (equal? f (□))
   (put-H H)
   (put-C (FCxt (□)))
   ---------------------------------- "chc12"
   `((throw ,(? b? b)) →chc (,V ,b))         ])

(define-match-expander mkCHC
  (syntax-parser
    [(_ M H FCxt) #'(cons (cons M H) FCxt)])
  (syntax-parser
    [(_ M H FCxt) #'(cons (cons M H) FCxt)]))

;; (M H FCxt) → 𝒫((M H FCxt))
(define ⊢->chc (let-values ([(mrun reducer) (⊢->chc-rules)])
                 (match-λ
                  [(mkCHC M H FCxt)
                   (mrun FCxt H (reducer M))])))
(define ⊢->>chc (compose1 car (repeated ⊢->chc)))

;; M → (V ∪ ⊥)
(define/match (evalchc m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>chc (mkCHC M '() (□)))
     [(set (mkCHC (? b? b) '() (□)))
      b]
     [(set (mkCHC `(λ ,X ,M) '() (□)))
      'function]
     [(set (mkCHC `(throw ,(? b? b)) '() (□)))
      `(err ,b)]
     [x (error 'evalchc "invalid final state: ~s" x)])]
  [_ (error 'evalchc "invalid input: ~s" m)])


(module+ test
  (check-exn #rx"invalid input" (λ () (evalchc '(+ 1 x))))
  (check-equal? (evalchc '(+ ((λ x x) 8) 2)) 10)
  (check-equal? (evalchc '((λ x x) (λ x x))) 'function)
  
  (check-equal? (evalchc '(add1 (λ x x))) '(err 0))
  (check-equal? (evalchc '(/ 3 0)) '(err 0))

  (check-equal? (⊢->>chc (mkCHC '(+ (- 4 (throw 1)) (throw 2)) '() (□)))
                (set (mkCHC '(throw 1) '() (□))))

  (check-equal? (evalchc '(catch (add1 (/ 3 0)) with (λ x (add1 x)))) 1)  
  (check-equal? (evalchc '(catch (+ (* 4 2) (throw 3)) with (λ x (add1 x)))) 4))

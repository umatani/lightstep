#lang racket/base
(require lightstep/base lightstep/syntax lightstep/transformers
         lightstep/inference
         (only-in "cc.rkt" □ [⊢->cc′-rules orig-⊢->cc′-rules] mkCC)
         (only-in "e-iswim.rkt" δ [δ-rules orig-δ-rules])
         (only-in "h-iswim.rkt"
                  [H-ISWIM orig-H-ISWIM] FV subst FCxt
                  [δerr-rules orig-δerr-rules])
         (only-in "h-iswim-std.rkt" ECxt))

(module+ test (require rackunit))

;;=============================================================================
;; 8.3 The Handler CC Machine

(define-language H-ISWIM #:super orig-H-ISWIM)

;; to match the monad
(define-inference (δ-rules) #:super [(orig-δ-rules δ)]
  #:monad (StateT #f (NondetT ID)))

(define-inference (δerr-rules) #:super [(orig-δerr-rules δ)]
  #:monad (StateT #f (NondetT ID)))

(define-inference (⊢->cc-rules) #:super [(orig-⊢->cc′-rules)]
  #:do [(define rδ    (reducer-of (δ-rules)))
        (define rδerr (reducer-of (δerr-rules)))]
  #:forms ([`(,i:i →cc   ,o:o) #:where o ← (⊢->cc-rules i)]
           [`(,i   →δ    ,o  ) #:where o ← (rδ          i)]
           [`(,i   →δerr ,o  ) #:where o ← (rδerr       i)])

  [`((,oⁿ ,@b) →δ ,(? b? b′))
   -------------------------------------- "ccffi"
   `((,(? oⁿ? oⁿ) ,(? b? b) ...) →cc ,b′)        ]

  [`(,M →δerr (throw ,(? b? b)))
   ----------------------------- "cc7"
   `(,M →cc (throw ,b))               ]

  [(and x (FCxt (□))) ← get
   #:when (not (equal? x (□)))
   (put (□))
   ----------------------------------- "cc8"
   `((throw ,(? b? b)) →cc (throw ,b))      ]

  [(ECxt (□)) ← get
   (put (ECxt `(catch ,(□) with (λ ,X ,M′))))
   ------------------------------------------ "cc9"
   `((catch ,M with (λ ,X ,M′)) →cc ,M)            ]

  [(ECxt `(catch ,(□) with (λ ,X ,M))) ← get
   (put (ECxt (□)))
   ----------------------------------------- "cc10"
   `(,V →cc ,V)                                    ]

  [(ECxt `(catch ,f with (λ ,X ,M))) ← get
   #:when (not (equal? f (□)))
   (put (ECxt `(catch ,(□) with (λ ,X ,M))))
   ----------------------------------------- "cc11"
   `((throw ,(? b? b)) →cc (throw ,b))             ]

  [(ECxt `(catch ,(□) with (λ ,X ,M))) ← get
   (put (ECxt (□)))
   ----------------------------------------- "cc12"
   `((throw ,(? b? b)) →cc ((λ ,X ,M) ,b))         ])

(define ⊢->cc (let-values ([(mrun reducer) (⊢->cc-rules)])
                (match-λ
                 [(mkCC M ECxt)
                  (mrun ECxt (reducer M))])))
(define ⊢->>cc (compose1 car (repeated ⊢->cc)))

(define/match (evalcc+h m)
  [M
   #:when (∅? (FV M))
   (match (⊢->>cc (mkCC M (□)))
     [(set (mkCC (? b? b) (□)))
      b]
     [(set (mkCC `(λ ,X ,M) (□)))
      'function]
     [(set (mkCC `(throw ,(? b? b)) (□)))
      `(err ,b)]
     [x (error 'evalcc+h "invalid final state: ~s" x)])]
  [_ (error 'evalcc+h "invalid input: ~s" m)])

(module+ test
  (check-exn #rx"invalid input" (λ () (evalcc+h '(+ 1 x))))
  (check-equal? (evalcc+h '(+ ((λ x x) 8) 2)) 10)
  (check-equal? (evalcc+h '((λ x x) (λ x x))) 'function)
  
  (check-equal? (evalcc+h '(add1 (λ x x))) '(err 0))
  (check-equal? (evalcc+h '(/ 3 0)) '(err 0))

  (check-equal? (⊢->>cc (mkCC '(+ (- 4 (throw 1)) (throw 2)) (□)))
                (set (mkCC '(throw 1) (□))))

  (check-equal? (evalcc+h '(catch (add1 (/ 3 0)) with (λ x (add1 x)))) 1)  
  (check-equal? (evalcc+h '(catch (+ (* 4 2) (throw 3)) with (λ x (add1 x)))) 4))

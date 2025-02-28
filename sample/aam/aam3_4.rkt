#lang racket/base
(require (for-syntax racket/base
                     (only-in syntax/parse syntax-parser id))
         (only-in racket/unit invoke-unit)
         lightstep/base
         (only-in "common.rkt" mmap-ext mmap-lookup sequence)
         (only-in "aam1-3_3.rkt" PCF δ)
         rackunit)

(require (only-in (submod "aam1-3_3.rkt" test) fact-5))


;; Abstracting Abstract Machines from:
;;   https://dvanhorn.github.io/redex-aam-tutorial/

;;-----------------------------------------------------------------------------
;; 3.4 Evaluation

(module+ PCF⇓
  (provide PCF⇓)

  (define-language PCF⇓ #:super PCF
    [V ∷=
       N O
       `(,L ,(? ρ?))
       `((μ [,X : ,T] ,L) ,(? ρ?))]
    [ρ ∷= (? map?)])

  (define-reduction (⇓-rules ⇓)
    [`(,N ,(? ρ?))
     ; -->
     N]

    [`(,O ,(? ρ?))
     ; -->
     O]

    [`(,L ,(? ρ? ρ))
     ; -->
     `(,L ,ρ)]

    [`((μ [,X : ,T] ,L) ,(? ρ? ρ))
     ; -->
     `((μ [,X : ,T] ,L) ,ρ)]

    [`(,X ,(? ρ? ρ))
     ; where
     V ← (for/monad+ ([V (in-set (mmap-lookup ρ X))])
           (return V))
     ; -->
     V]

    [`((if0 ,M₀ ,M₁ ,M₂) ,(? ρ? ρ))
     ; where
     N ← (⇓ `(,M₀ ,ρ))
     M ≔ (if (zero? N) M₁ M₂)
     V ← (⇓ `(,M ,ρ))
     ; -->
     V]

    [`((,M₀ ,M₁ ...) ,(? ρ? ρ))
     ; where
     O ← (⇓ `(,M₀ ,ρ))
     `(,N₁ ...) ← (sequence (map (λ (m) (⇓ `(,m ,ρ))) M₁))
     N ≔ (δ `(,O ,@N₁))
     ; -->
     N]

    [`((,M₀ ,M₁ ...) ,(? ρ? ρ))
     ; where
     `((λ ([,X₁ : ,T] ...) ,M) ,(? ρ? ρ₁)) ← (⇓ `(,M₀ ,ρ))
     `(,V₁ ...) ← (sequence (map (λ (m) (⇓ `(,m ,ρ))) M₁))
     V ← (⇓ `(,M ,(apply mmap-ext ρ₁ (map list X₁ V₁))))
     ; -->
     V]

    [`((,M₀ ,M₁ ...) ,(? ρ? ρ))
     ; where
     (and f `((μ [,X : ,T₁] (λ ([,X₁ : ,T₂] ...) ,M))
              ,(? ρ? ρ₁))) ← (⇓ `(,M₀ ,ρ))
     `(,V₁ ...) ← (sequence (map (λ (m) (⇓ `(,m ,ρ))) M₁))
     V ← (⇓ `(,M ,(apply mmap-ext ρ₁ `[,X ,f] (map list X₁ V₁))))
     ; -->
     V])

  (define (⇓ M ρ) (let ()
                    (define ⇓ (call-with-values
                               (λ () (invoke-unit (⇓-rules ⇓)))
                               compose1))
                    (⇓ `(,M ,ρ))))

  (define (⇓? M ρ v) (∈ v (⇓ M ρ)))

  (check-equal? (⇓ fact-5 (↦)) (set 120))
  (check-true (⇓? fact-5 (↦) 120)))


;;-----------------------------------------------------------------------------
;; 3.5 A brief aside on the caveats of language extensions

(module+ §3.5
  (module+ L₀
    (provide L₀ (reduction-out r₀-rules) to-five (reduction-out r₁-rules))
    
    (define-language L₀
      [M ∷= (? number?)])
    (define-reduction (r₀-rules)
      [M 5])
    (define r₀ (call-with-values
                (λ () (invoke-unit (r₀-rules)))
                compose1))
    (check-equal? (r₀ 7) (set 5))

    (define (to-five m)
      (match m
        [M 5]))
    (define-reduction (r₁-rules)
      [M (to-five M)])
    (define r₁ (call-with-values
                (λ () (invoke-unit (r₁-rules)))
                compose1))
    (check-equal? (r₁ 7) (set 5)))

  (module+ L₁
    (require (submod ".." L₀))

    (define-language L₁ #:super L₀
      [M ∷= .... (? string?)])
    (check-true (M? 5))
    (check-true (M? "five"))
    (define-reduction (r₀′-rules) #:super (r₀-rules))
    (define r₀′ (call-with-values
                 (λ () (invoke-unit (r₀′-rules)))
                 compose1))
    (check-equal? (r₀′ "seven") (set 5))

    (define-reduction (r₁′-rules) #:super (r₁-rules))
    (define r₁′ (call-with-values
                 (λ () (invoke-unit (r₁′-rules)))
                 compose1))
    (check-exn #rx"no matching clause" (λ () (r₁′ "seven")))))


;;-----------------------------------------------------------------------------
;; 3.6 Explicit substitutions

(module+ PCFρ
  (require (submod ".." PCF⇓))
  (provide PCFρ (reduction-out vρ-rules) injρ)

  (define-language PCFρ #:super PCF⇓
    [C ∷=
       V
       `(,M ,(? ρ?))
       `(if0 ,C₀ ,C₁ ,C₂)
       `(,C₀ ,C₁ ...)])

  (define-nondet-match-expander ECxt
    (syntax-parser
      [(ECxt □:id)
       #'(... (cxt ECxt □
                   `(,V ... ,(? C? □) ,C ...)
                   `(if0 ,(? C? □) ,C₁ ,C₂)))]))

  (define-reduction (vρ-rules)
    [`((if0 ,M ...) ,(? ρ? ρ))
     ; -->
     `(if0 ,@(map (λ (m) `(,m ,ρ)) M))
     "ρ-if"]

    [`((,M ...) ,(? ρ? ρ))
     ; -->
     `(,@(map (λ (m) `(,m ,ρ)) M))
     "ρ-app"]

    [`(,O ,(? ρ? ρ))
     ; -->
     O
     "ρ-op"]

    [`(,N ,(? ρ? ρ))
     ; -->
     N
     "ρ-num"]

    [`(,X ,(? ρ? ρ))
     ; where
     V ← (for/monad+ ([v (mmap-lookup ρ X)]) (return v))
     ; -->
     V
     "ρ-x"]

    [`(((λ ([,X : ,T] ...) ,M) ,(? ρ? ρ)) ,V ...)
     ; -->
     `(,M ,(apply mmap-ext ρ (map list X V) ))
     "β"]

    [`(,(and f `((μ [,X′ : ,T′] (λ ([,X : ,T] ...) ,M)) ,(? ρ? ρ))) ,V ...)
     ; -->
     `(,M ,(apply mmap-ext ρ `[,X′ ,f] (map list X V)))
     "rec-β"]

    [`(,O ,V ...)
     ; where
     V₁ ≔ (δ `(,O ,@V))
     ; -->
     V₁
     "δ"]

    [`(if0 0 ,C₁ ,C₂)
     ; -->
     C₁
     "if-t"]

    [`(if0 ,N ,C₁ ,C₂)
     #:when (not (equal? 0 N))
     ; -->
     C₂
     "if-f"])
  
  (define-reduction (-->vρ-rules -->vρ) #:super (vρ-rules)
    [(ECxt c)
     ; where
     C′ ← (-->vρ c)
     ; -->
     (ECxt C′)
     "EC"])

  (define -->vρ (call-with-values
                 (λ () (invoke-unit (-->vρ-rules -->vρ)))
                 compose1))

  (define (injρ M)
    `(,M ,(↦)))

  (check-equal? (car ((repeated -->vρ) (injρ fact-5))) (set 120)))

;;-----------------------------------------------------------------------------
;; 3.7 Eval/Continue/Apply machine

(module+ PCFς
  (require (submod ".." PCFρ))
  (provide PCFς  (reduction-out -->vς-rules) injς)

  (define-language PCFς #:super PCFρ
    [F ∷=
       `(,V ... □ ,C ...)
       `(if0 □ ,C₁ ,C₂)]
    [K ∷= `[,F ...]]
    [S ∷= ; serious terms S ∩ V = ∅, C = S ∪ V
       `(,N ,(? ρ?))
       `(,O ,(? ρ?))
       `(,X ,(? ρ?))
       `((,M ,M′ ...) ,(? ρ?))
       `((if0 ,M₀ ,M₁ ,M₂) ,(? ρ?))
       `(if0 ,C₀ ,C₁ ,C₂)
       `(,C ,C′ ...)]
    [ς ∷= `(,C ,K) V])

  (define-reduction (-->vς-rules)
    #:do [(define-reduction (rules) #:super (vρ-rules))
          (define vρ (call-with-values
                       (λ () (invoke-unit (rules)))
                       compose1))]
    ; Apply
    [`(,C ,K)
     ; where
     C′ ← (vρ C)
     ; -->
     `(,C′ ,K)
     "ap"]

    ; Eval
    [`((if0 ,S₀ ,C₁ ,C₂) [,F ...])
     ; -->
     `(,S₀ [(if0 □ ,C₁ ,C₂) ,@F])
     "ev-if"]

    [`((,V ... ,S ,C ...) [,F ...])
     ; -->
     `(,S [(,@V □ ,@C) ,@F])
     "ev-app"]

    ; Continue
    [`(,V [])
     ; -->
     V
     "halt"]

    [`(,V [(if0 □ ,C₁ ,C₂) ,F ...])
     ; -->
     `((if0 ,V ,C₁ ,C₂) [,@F])
     "co-if"]

    [`(,V [(,V₀ ... □ ,C₀ ...) ,F ...])
     ; -->
     `((,@V₀ ,V ,@C₀) [,@F])
     "co-app"])

  (define -->vς (call-with-values
                 (λ () (invoke-unit (-->vς-rules)))
                 compose1))

  (define (injς M)
    `(,(injρ M) []))
  
  (check-equal? (car ((repeated -->vς) (injς fact-5)))
                (set 120))
  (check-equal? (car ((repeated -->vς) (injς '((λ ([x : num]) x) (add1 5)))))
                (set 6)))

;;-----------------------------------------------------------------------------
;; 3.8 Heap-allocated bindings

(module+ PCFσ
  (require (only-in (submod ".." PCFρ) vρ-rules vρ-rules-info)
           (submod ".." PCFς))
  (provide PCFσ (reduction-out -->vσ-rules) injσ
           formals (reduction-out alloc-rules) alloc)

  (define-language PCFσ #:super PCFς
    [Σ ∷= (? map?)]
    [A ∷= (? (λ (_) #t))]
    [σ ∷= `(,(? ς?) ,Σ) V])
 
  (define-reduction (-->vσ-rules)
    #:do [(define-reduction (-->vς′-rules) #:super (-->vς-rules)
            #:do[;; remove rules manually
                 (define-reduction (vρ′-rules) #:super (vρ-rules)
                   [x #:when #f x "ρ-x"]
                   [x #:when #f x "β"]
                   [x #:when #f x "rec-β"])
                 (define vρ′ (call-with-values
                                (λ () (invoke-unit (vρ′-rules)))
                                compose1))]
            ; Apply
            [`(,C ,K)
             ; where
             C′ ← (vρ′ C)
             ; -->
             `(,C′ ,K)
             "ap"])

          (define -->vς′ (call-with-values
                           (λ () (invoke-unit (-->vς′-rules)))
                           compose1))]
    [`(,(? ς? ς) ,Σ)
     ; where
     (? ς? ς′) ← (-->vς′ ς)
     ; -->
     `(,ς′ ,Σ)]

    [`(,N ,Σ)
     ; -->
     N
     "discard-Σ-N"]

    [`(,O ,Σ)
     ; -->
     O
     "discard-Σ-O"]

    [`(((,X ,(? ρ? ρ)) ,K) ,Σ)
     ; where
     A ← (mmap-lookup ρ X)
     V ← (mmap-lookup Σ A)
     ; -->
     `((,V ,K) ,Σ)
     "ρ-x"]

    [(and σ `(((((λ ([,X : ,T] ...) ,M) ,(? ρ? ρ)) ,V ...) ,K) ,Σ))
     ; where
     `(,A ...) ≔ (alloc σ)
     ; -->
     `(((,M ,(apply mmap-ext ρ (map list X A))) ,K)
       ,(apply mmap-ext Σ (map list A V)))
     "β"]

    [(and σ `(((,(and f `((μ [,X′ : ,T′]
                               (λ ([,X : ,T] ...) ,M)) ,(? ρ? ρ))) ,V ...)
                ,K) ,Σ))
     ; where
     `(,A′ ,A ...) ≔ (alloc σ)
     ; -->
     `(((,M ,(apply mmap-ext ρ `[,X′ ,A′] (map list X A))) ,K)
       ,(apply mmap-ext Σ `[,A′ ,f] (map list A V)))
     "rec-β"])

  (define -->vσ (call-with-values
                 (λ () (invoke-unit (-->vσ-rules)))
                 compose1))

  (define (injσ M)
    `(,(injς M) ,(↦)))

  (define (formals M)
    (match M
      [`(λ ([,X : ,T] ...) ,M)
       `(,@X)]
      [`(μ [,X′ : ,T′] ,L)
       (match-let ([`(,X ...) (formals L)])
         `(,X′ ,@X))]))

  (define-reduction (alloc-rules)
    [`((((,M ,(? ρ?)) ,V ...) ,K) ,Σ)
     (map (λ (x) (list x (gensym x))) (formals M))])

  (define (alloc σ) (let ([al (call-with-values
                                (λ () (invoke-unit (alloc-rules)))
                                compose1)])
                       (match (al σ)
                         [(set x) x])))

  ;(alloc `(((((λ ([y : num] [z : num]) y) ,(↦)) 5 7) []) ,(↦)))
  ;(-->vσ `(((((λ ([y : num] [z : num]) y) ,(↦)) 5 7) []) ,(↦)))

  (check-equal?  (car ((repeated -->vσ) (injσ fact-5))) (set 120)))

;;-----------------------------------------------------------------------------
;; 3.9 Abstracting over alloc

(module+ PCFσ/alloc
  (require (only-in (submod ".." PCFρ) vρ-rules vρ-rules-info)
           (only-in (submod ".." PCFς) -->vς-rules -->vς-rules-info)
           (rename-in (submod ".." PCFσ) [PCFσ orig-PCFσ]))
  (provide (reduction-out -->vσ/alloc-rules))

  (define-language PCFσ #:super orig-PCFσ)

  (define-reduction (-->vσ/alloc-rules alloc) #:super (-->vσ-rules))

  (define -->vσ (call-with-values
                  (λ () (invoke-unit (-->vσ/alloc-rules alloc)))
                  compose1))

  (check-equal?  (car ((repeated -->vσ) (injσ fact-5))) (set 120))

  (define (alloc-gensym σ)
    (match σ
      [`((((,M ,(? ρ?)) ,V ...) ,K) ,Σ)
       (map gensym (formals M))]))  

  (let ()
    (define --> (call-with-values
                 (λ () (invoke-unit (-->vσ/alloc-rules alloc-gensym)))
                 compose1))
    ;(car ((repeated -->) (injσ '((λ ([x : num]) (λ ([y : num]) x)) 100))))
    (check-equal? (car ((repeated -->) (injσ fact-5))) (set 120)))

  (define (alloc-nat σ)
    (match σ
      [`((((,M ,(? ρ?)) ,V ...) ,K) ,Σ)
       (let ([n (add1 (apply max 0 (set→list (keys Σ))))])
         (build-list (length (formals M))
                     (λ (i) (+ i n))))]))  

  (let ()
    (define --> (call-with-values
                 (λ () (invoke-unit (-->vσ/alloc-rules alloc-nat)))
                 compose1))
    ;(car ((repeated -->) (injσ '((λ ([x : num]) (λ ([y : num]) x)) 100))))
    (check-equal? (car ((repeated -->) (injσ fact-5))) (set 120))))

;;-----------------------------------------------------------------------------
;; 3.10 Heap-allocated continuations

(module+ PCFσ*
  (require (only-in (submod ".." PCFρ) vρ-rules vρ-rules-info)
           (only-in (submod ".." PCFς) -->vς-rules -->vς-rules-info)
           (only-in (submod ".." PCFσ)
                    PCFσ injσ formals alloc-rules alloc-rules-info)
           (submod ".." PCFσ/alloc))

  (define-language PCFσ* #:super PCFσ
    [K ∷= '() `(,F ,A)]
    [U ∷= V K])

  (define-reduction (alloc*-rules) #:super (alloc-rules)
    [`(((if0 ,S₀ ,C₁ ,C₂) ,K) ,Σ)
     `(((if0 □ ,C₁ ,C₂) ,(gensym 'if0)))]
    [`(((,V ... ,S ,C ...) ,K) ,Σ)
     `(((,@V □ ,@C) ,(gensym 'app)))])

  (define (alloc* σ) (let ([al (call-with-values
                                 (λ () (invoke-unit (alloc*-rules)))
                                 compose1)])
                        (match (al σ)
                          [(set x) x])))

  ;; (alloc* `(((if0 ((add1 2) ,(↦)) (3 ,(↦)) (4 ,(↦))) ()) ,(↦)))
  ;; (alloc* `(((((λ ([y : num]) y) ,(↦)) ((add1 2) ,(↦))) ()) ,(↦)))
  ;; (alloc* `(((((λ ([y : num] [z : num]) y) ,(↦)) 5 7) ()) ,(↦)))

  (define-reduction (-->vσ*/alloc-rules alloc*)
    #:super (-->vσ/alloc-rules alloc*)

    ; Eval
    [(and σ `(((if0 ,S₀ ,C₁ ,C₂) ,K) ,Σ))
     ; where
     `(,A) ≔ (alloc* σ)
     ; -->
     `((,S₀ ((if0 □ ,C₁ ,C₂) ,A)) ,(mmap-ext Σ `[,A ,K]))
     "ev-if"]

    [(and σ `(((,V ... ,S ,C ...) ,K) ,Σ))
     ; where
     `(,A) ≔ (alloc* σ)
     ; -->
     `((,S ((,@V □ ,@C) ,A)) ,(mmap-ext Σ `[,A ,K]))
     "ev-app"]

    ; Continue
    [`((,V ((if0 □ ,C₁ ,C₂) ,A)) ,Σ)
     ; where
     K ← (mmap-lookup Σ A)
     ; -->
     `(((if0 ,V ,C₁ ,C₂) ,K) ,Σ)
     "co-if"]

    [`((,V ((,V₀ ... □ ,C₀ ...) ,A)) ,Σ)
     ; where
     K ← (mmap-lookup Σ A)
     ; -->
     `(((,@V₀ ,V ,@C₀) ,K) ,Σ)
     "co-app"])

  (define -->vσ* (call-with-values
                   (λ () (invoke-unit (-->vσ*/alloc-rules alloc*)))
                   compose1))

  (check-equal? (car ((repeated -->vσ*) (injσ fact-5))) (set 120)))

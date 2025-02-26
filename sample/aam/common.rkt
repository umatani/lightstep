#lang racket/base
(require lightstep/base
         (for-syntax racket/base syntax/parse
                     (only-in syntax/stx stx-map))
         (only-in lightstep/transformers define-monad)
         (prefix-in r: (only-in racket/set mutable-set set-member? set-add!)))
(provide match? mmap mmap-lookup mmap-lookup? mmap-ext1 mmap-ext
         sequence cxt reachable?)

(module+ test (require rackunit))

;; Abstracting Abstract Machines from:
;;   https://dvanhorn.github.io/redex-aam-tutorial/


;;=============================================================================
;; Utils

(define-syntax (match? stx)
  (syntax-parse stx
    [(_ p x)
     #'(match x
         [p #t]
         [_ #f])]))

;; multi-map: A → P(B)

(define (mmap . bs)
  (match bs
    [`([,xs ,ts] ...)
     (for/fold ([m map-∅])
               ([x xs]
                [t ts])
       (m x (∪ (if (map-∈ x m)
                 (m x)
                 ∅)
               (set t))))]))

(define (mmap-lookup m x)
  (match m
    [(↦ [x ts]) ts]
    [_ ∅]))

(define (mmap-lookup? m x t)
  (∈ t (mmap-lookup m x)))

(module+ test
  (check-true  (mmap-lookup? (mmap '[x 1] '[y 2] '[x 3]) 'x 1))
  (check-false (mmap-lookup? (mmap '[x 1] '[y 2] '[x 3]) 'x 2))
  (check-true  (mmap-lookup? (mmap '[x 1] '[y 2] '[x 3]) 'x 3))
  (check-equal? (mmap-lookup (mmap '[x 1] '[y 2] '[x 3]) 'x) (set 1 3)))

(define (mmap-ext1 m x t)
  (match m
    [(↦ [x (set)])   (m x (set t))]
    [(↦ [x (set _)]) (m x (set t))]
    [(↦ [x (set _ _ ...)])
     (error 'mmap-ext1 "multiple bindings of ~s in ~s" x m)]
    [(↦) (m x (set t))]))

(define (mmap-ext m . bs)
  (match bs
    ['() m]
    [`([,x ,t] ,@bs′) (mmap-ext1 (apply mmap-ext m bs′) x t)]))

;; mapM : Monad m => (a -> m b) -> [a] -> m [b]
(define (mapM #:monad [M ReduceM] f as)
  (define-monad M)
  (foldr (λ (a r)
           (do x  ← (f a)
               xs ← r
               (return (cons x xs))))
         (return '())
         as))

;; sequence : Monad m => [m a] -> m [a]
(define (sequence #:monad [M ReduceM] as)
  (mapM #:monad M (λ (a) a) as))

(begin-for-syntax
  (define (with-ctor/list stx)
    (syntax-parse stx
      [() #'(() '())]

      [(p₀ (~datum ...) p₁ ...)
       #:with (p₀′ c₀) (with-ctor #'p₀)
       #:with (p₀″ n₀) (if (identifier? #'c₀)
                         #'(p₀′ c₀)
                         (with-syntax ([(n) (generate-temporaries #'(n))])
                           #'((and n p₀′) n)))
       #:with ((p₁′ ...) c₁) (with-ctor/list #'(p₁ ...))
       #'((p₀″ (... ...) p₁′ ...) (append n₀ c₁))]

      [(p₀ p₁ ...)
       #:with (p₀′ c₀) (with-ctor #'p₀)
       #:with ((p₁′ ...) c₁) (with-ctor/list #'(p₁ ...))
       #'((p₀′ p₁′ ...) (cons c₀ c₁))]

      [p (raise-syntax-error 'with-ctor/list "unknown pattern" #'p)]))

  (define (with-ctor/quasi stx)
    (syntax-parse stx
      #:literals (unquote unquote-splicing)

      [() #'(() '())]

      [x:id #'(x 'x)]

      [(unquote p)
       #:with (p′ c) (with-ctor #'p)
       #'((unquote p′) c)]

      [((unquote-splicing p₀) qp₁ ...)
       #:with (p₀′ c₀) (with-ctor #'p₀)
       #:with (p₀″ n₀) (if (identifier? #'c₀)
                         #'(p₀′ c₀)
                         (with-syntax ([(n) (generate-temporaries #'(n))])
                           #'((unquote (and n (quasiquote p₀′))) n)))
       #:with ((qp₁′ ...) c₁) (with-ctor/quasi #'(qp₁ ...))
       #'(((unquote-splicing p₀″) qp₁′ ...) (append n₀ c₁))]

      [(qp₀ (~datum ...) qp₁ ...)
       #:with (qp₀′ c₀) (with-ctor/quasi #'qp₀)
       #:with (qp₀″ n₀) (if (identifier? #'c₀)
                          #'(qp₀′ c₀)
                          (with-syntax ([(n) (generate-temporaries #'(n))])
                            #'((unquote (and n (quasiquote qp₀′))) n)))
       #:with ((qp₁′ ...) c₁) (with-ctor/quasi #'(qp₁ ...))
       #'((qp₀″ (... ...) qp₁′ ...) (append n₀ c₁))]

      [(qp₀ qp₁ ...)
       #:with (qp₀′ c₀) (with-ctor/quasi #'qp₀)
       #:with ((qp₁′ ...) c₁) (with-ctor/quasi #'(qp₁ ...))
       #'((qp₀′ qp₁′ ...) (cons c₀ c₁))]

      [b:boolean #'(b b)]
      [c:char    #'(c c)]
      [k:keyword #'(k k)]
      [n:number  #'(n n)]
      [s:str     #'(s s)]

      [p (raise-syntax-error 'with-ctor/quasi "unknown pattern" #'p)]))
  
  (define (with-ctor stx)
    (syntax-parse stx
      #:literals (quote quasiquote list cons)

      [(quote x)
       #'((quote x) (quote x))]

      [(quasiquote qp)
       #:with (qp′ c) (with-ctor/quasi #'qp)
       #'((quasiquote qp′) c)]

      [(list p ...)
       #:with ((p′ ...) c) (with-ctor/list #'(p ...))
       #'((list p′ ...) c)]

      [(cons p₀ p₁)
       #:with (p₀′ c₀) (with-ctor #'p₀)
       #:with (p₁′ c₁) (with-ctor #'p₁)
       #'((cons p₀′ p₁′) (cons c₀ c₁))]

      [((~datum ?) e x:id)  ;; tiny hack
       #'((? e x) x)]

      [((~datum ?) e p ...) ;; general case
       #:with (n) (generate-temporaries #'(n))
       #'((? e n p ...) n)]

      [x:id
       (if (category-id? #'x)
         (with-syntax ([(n) (generate-temporaries #'(n))])
           #'((and n x) n))
         #'(x x))]

      [b:boolean #'(b b)]
      [c:char    #'(c c)]
      [k:keyword #'(k k)]
      [n:number  #'(n n)]
      [s:str     #'(s s)]

      [p (raise-syntax-error 'with-ctor "unknown pattern" #'p)]))

  (define (cxt1 stx)
    (syntax-parse stx
      [(C:id hole:id p)
       #:with (p′ c) (with-ctor #'p)
       #'(and p (app (match-λ [p′ (λ (hole) c)]) C))])))

(define-nondet-match-expander cxt
  (syntax-parser
    [(_ C:id hole:id p ...)
     #:with (p′ ...) (stx-map (λ (p) (cxt1 #`(C hole #,p))) #'(p ...))
     #'(nondet p′ ...)]))

;; (match '(1 2 3)
;;   [`(,(? number? A) ,□ ,(? number?))
;;    `(,A ,□ ,A)])

;; (nondet-match NondetM '(1 2 3)
;;               [(nondet `(,(? number? A) ,□ ,(? number?)))
;;                `(,A ,□ ,A)])

;; (define A? number?)

;; (nondet-match NondetM '(1 2)
;;               [(cxt Cxt □ `(,A ,□))
;;                (Cxt `(,A ,□ ,A))])





(struct Queueof (head tail) #:transparent #:mutable
  #:constructor-name Queue)

(define (make-queue) (Queue '() '()))

(define (queue-empty? q)
  (and (null? (Queueof-head q)) (null? (Queueof-tail q))))

(define (enqueue! q a)
  (set-Queueof-tail! q (cons a (Queueof-tail q))))

(define (dequeue! q)
  (when (queue-empty? q)
    (error 'dequeue! "queue is empty"))
  (when (null? (Queueof-head q))
    (set-Queueof-head! q (reverse (Queueof-tail q)))
    (set-Queueof-tail! q '()))
  (begin0
      (car (Queueof-head q))
    (set-Queueof-head! q (cdr (Queueof-head q)))))

(define (reachable? → ς-init ς-final)
  (define wl (make-queue))
  (define Σ (r:mutable-set))

  (define (search)
    (if (r:set-member? Σ ς-final)
      #t
      (if (queue-empty? wl)
        #f
        (begin
          (for ([ς′ (in-set (→ (dequeue! wl)))]
                #:unless (r:set-member? Σ ς′))
            (enqueue! wl ς′)
            (r:set-add! Σ ς′))
          (search)))))
  (enqueue! wl ς-init)
  (r:set-add! Σ ς-init)
  (search))

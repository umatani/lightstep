#lang racket/base
(require (for-syntax racket/base syntax/parse)
         (only-in racket/hash hash-union)
         (only-in racket/match define-match-expander)
         (only-in racket/mutability immutable-hash?)
         (only-in "set.rkt" for/set [∈ s:∈]))
(provide ↦ map? ∅ ∅? ∈ size map=? dom rng ⊔ map-update map-remove
         map-map map-filter restrict map->list list->map
         hash->map for/map in-map
         (rename-out [map->list map→list]
                     [list->map list→map]
                     [repl->hash map->hash]
                     [repl->hash map→hash]
                     [hash->map hash→map]))

;; ============================================================================
;; Finite map: α ↦ β

;; α   → β
;; α β → (α ↦ β)
(struct repl (>hash)
  #:transparent  ;; for equal?
  #:property
  prop:procedure
  (case-λ
   [(m x) 
    (if (∈ x m)
      (hash-ref (repl->hash m) x)
      (error 'map "has no value for key: ~s" x))]
   [(m x v)
    (repl (hash-set (repl->hash m) x v))])
  #:methods gen:custom-write
  [(define (write-proc m port mode)
     (when mode (write-string "{" port))
     (let ([es (hash->list (repl->hash m))]
           [recur (case mode
                    [(#t) write]
                    [(#f) display]
                    [else (λ (p port) (print p port mode))])])
       (unless (zero? (length es))
         (recur (caar es) port)
         (write-string " ↦ " port)
         (recur (cdar es) port)
         (for-each (λ (e)
                     (write-string ", " port)
                     (recur (car e) port)
                     (write-string " ↦ " port)
                     (recur (cdr e) port))
                   (cdr es))))
     (when mode (write-string "}" port)))])

;; List([α . β]) → (α ↦ β)
(define (list->map l)
  (repl (make-immutable-hash l)))

;; [α β] ... → (α ↦ β)
(define-match-expander ↦
  (λ (stx)
    (syntax-case stx (... ...)
      [(_ (x y) (... ...))
       #'(? map? (app (λ (x) (for/fold ([kvs (cons '() '())])
                                       ([kv (map->list x)])
                               (cons (cons (car kv) (car kvs))
                                     (cons (cdr kv) (cdr kvs)))))
                      (cons x y)))]
      [(_ (x y) ...)
       #'(? map? (app repl->hash (hash* (x y) ...)))]))
  (λ (stx)
    (syntax-case stx ()
      [(_ (x y) ...)
       #'(list->map (list (cons x y) ...))])))

;; Any → Boolean
(define map? repl?)

;; (α ↦ β)
(define ∅ (↦))

;; (α ↦ β) → Boolean
(define (∅? m)
  (hash-empty? (repl->hash m)))

;; α (α ↦ β) → Boolean
;;   (α ↦ β) → Seq([α β])
(define ∈
  (case-λ
   [(k m) (hash-has-key? (repl->hash m) k)]
   [(  m) (in-map m)]))

;; (α ↦ β) → Nat
(define (size m)
  (hash-count (repl->hash m)))

;; (α ↦ β) (α ↦ β) → Boolean
(define (map=? m₁ m₂)
  (and (= (size m₁) (size m₂))
       (for/and ([(k₁ v₁) (∈ m₁)])
         (equal? v₁ (m₂ k₁)))))

;; (α ↦ β) → 𝒫(α)
(define (dom m)
  (for/set ([(k _) (∈ m)]) k))

;; (α ↦ β) → 𝒫(β)
(define (rng m)
  (for/set ([(_ v) (∈ m)]) v))

;; (α ↦ β) ...+ #:xombine (λ (β β) β) → (α ↦ β)
(define (⊔ m₁ #:combine [cod-⊔ (λ (_ x) x)] . mₙ)
  (repl (apply hash-union
               (repl->hash m₁)
               (foldl (λ (m a) (cons (repl->hash m) a)) '() mₙ)
               #:combine cod-⊔)))

;; (α ↦ β) α (β → β) [β | (→ β)] → (α ↦ β)
(define (map-update m k f [o (λ () (error 'map "has no value for key: ~s" k))])
  (hash->map (hash-update (repl->hash m) k f o)))

;; (α ↦ β) α → (α ↦ β)
(define (map-remove m k)
  (hash->map (hash-remove (repl->hash m) k)))

;; (α β → γ) (α ↦ β) → List(γ)
(define (map-map f m)
  (hash-map (repl->hash m) f))

;; (α β → Boolean) (α ↦ β) → (α ↦ β)
(define (map-filter p m)
  (for/map ([(k v) (∈ m)]
            #:when (p k v))
    (values k v)))

;; (α ↦ β) 𝒫(α) → (α ↦ β)
(define (restrict m ks)
  (map-filter (λ (k _) (s:∈ k ks)) m))

;; (α ↦ β) → List([α . β])
(define (map->list m)
  (hash->list (repl->hash m)))

;; Hash(α, β) → (α ↦ β)
(define (hash->map h)
  (if (immutable-hash? h)
    (repl h)
    (error 'hash->map "non-immutable: ~s" h)))

;; ... (values α β) ... → (α ↦ β)
(define-syntax (for/map stx)
  (syntax-parse stx
    [(_ (~optional (~seq #:combine cod-⊔) #:defaults ([cod-⊔ #'(λ (v′ v) v)]))
        (clause ...) defs+exprs ...+)
     (with-syntax ([original stx])
       #'(for/fold/derived original ([m ∅]) (clause ...)
           (let-values ([(k v) (let () defs+exprs ...)])
             (map-update m k (λ (v′) (cod-⊔ v′ v)) 'for/map-no-value))))]))

;; (α ↦ β) → Seq([α β])
(define (in-map m)
  (in-hash (repl->hash m)))


(module+ test
  (require rackunit)
  (define r ∅)
  (check-equal? ((r 'x 1) 'x) 1)
  (check-equal? ((r 'x 1) 'y 2) ((r 'y 2) 'x 1))
  (check-equal? (∈ 'x (r 'x 1)) #t)
  (check-equal? ('y . ∈ . (r 'x 1)) #f)
  (check-true
   (let ([l (for/list ([(k v) (∈ ((r 'x 1) 'y 2))])
              (cons k v))])
     (not (not (and (member (cons 'y 2) l) (member (cons 'x 1) l)))))))

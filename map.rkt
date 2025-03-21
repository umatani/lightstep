#lang racket/base
(require (for-syntax racket/base syntax/parse)
         (only-in racket/hash hash-union)
         (only-in racket/mutability immutable-hash?)
         (only-in "match.rkt" define-match-expander)
         (only-in "misc.rkt" unzip)
         (only-in "set.rkt" [-∈ set-∈] [-for/set for/set] [-in-set in-set]))
(provide -make (rename-out [map? ?]) -∅ -∅? -∈ -size =? -dom -rng
         -∪ -update -remove -map -filter -restrict
         ->set <-set ->list <-list <-hash
         -for/map -in-map
         (rename-out [->set      →set]
                     [<-set      ←set]
                     [->list     →list]
                     [<-list     ←list]
                     [repl->hash ->hash]
                     [repl->hash →hash]
                     [<-hash     ←hash]))
;; provided from lightstep/base with prefix `map-'
;; also, aliases are provided from lightstep/base:
;;   ↦        = map-make
;;   dom      = map-dom
;;   rng      = map-rng
;;   ⊔        = map-∪
;;   restrict = map-restrict
;;   for/map  = map-for/map
;;   in-map   = map-in-map
;;   set->map = map<-set
;;   set→map  = map←set
;;   set<-map = map->set
;;   set←map  = map→set

;; ============================================================================
;; Finite map: α ↦ β

;; α   → β
;; α β → (α ↦ β)
(struct repl (>hash)
  #:transparent  ;; for equal?
  #:property prop:sequence
  (λ (m) (-in-map m))
  #:property
  prop:procedure
  (case-λ
   [(m x) 
    (if (-∈ x m)
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
(define (<-list l)
  (repl (make-immutable-hash l)))

;; [α β] ... → (α ↦ β)
(define-match-expander -make
  (λ (stx)
    (syntax-case stx (... ...)
      [(_ (x y) ... [xs ys] (... ...))
       #'(? map? (app ->list
                      (list-no-order `(,x . ,y) ... (cons xs ys) (... ...))))]
      [(_ (x y) ... m (... ...))
       #'(? map? (app ->list
                      (list-no-order `(,x . ,y) ... m (... ...))))]
      [(_ (x y) ...)
       #'(? map? (app repl->hash (hash (x y) ...)))]))
  (λ (stx)
    (syntax-case stx ()
      [(_ (x y) ...)
       #'(<-list (list (cons x y) ...))])))

;; Any → Boolean
(define map? repl?)

;; (α ↦ β)
(define -∅ (-make))

;; (α ↦ β) → Boolean
(define (-∅? m)
  (hash-empty? (repl->hash m)))

;; α (α ↦ β) → Boolean
;;   (α ↦ β) → Seq([α β])
(define -∈
  (case-λ
   [(k m) (hash-has-key? (repl->hash m) k)]
   [(  m) (-in-map m)]))

;; (α ↦ β) → Nat
(define (-size m)
  (hash-count (repl->hash m)))

;; (α ↦ β) (α ↦ β) → Boolean
(define (=? m₁ m₂)
  (and (= (-size m₁) (-size m₂))
       (for/and ([(k₁ v₁) (-∈ m₁)])
         (equal? v₁ (m₂ k₁)))))

;; (α ↦ β) → 𝒫(α)
(define (-dom m)
  (for/set ([(k _) (-∈ m)]) k))

;; (α ↦ β) → 𝒫(β)
(define (-rng m)
  (for/set ([(_ v) (-∈ m)]) v))

;; (α ↦ β) ...+ #:xombine (λ (β β) β) → (α ↦ β)
(define (-∪ m₁ #:combine [cod-⊔ (λ (v′ v) v)] . mₙ)
  (repl (apply hash-union
               (repl->hash m₁)
               (foldl (λ (m a) (cons (repl->hash m) a)) '() mₙ)
               #:combine cod-⊔)))

;; (α ↦ β) α (β → β) [β | (→ β)] → (α ↦ β)
(define (-update m k f [o (λ () (error 'map "has no value for key: ~s" k))])
  (<-hash (hash-update (repl->hash m) k f o)))

;; (α ↦ β) α → (α ↦ β)
(define (-remove m k)
  (<-hash (hash-remove (repl->hash m) k)))

;; (α β → γ) (α ↦ β) → List(γ)
(define (-map f m)
  (hash-map (repl->hash m) f))

;; (α β → Boolean) (α ↦ β) → (α ↦ β)
(define (-filter p m)
  (-for/map ([(k v) (-∈ m)]
             #:when (p k v))
    (values k v)))

;; (α ↦ β) 𝒫(α) → (α ↦ β)
(define (-restrict m ks)
  (-filter (λ (k _) (set-∈ k ks)) m))

;; (α ↦ β) → 𝒫([α . β])
(define (->set m)
  (for/set ([(k v) (-in-map m)])
    (cons k v)))

;; 𝒫([α . β]) → (α ↦ β)
(define (<-set s)
  (-for/map ([x (in-set s)])
    (values (car x) (cdr x))))

;; (α ↦ β) → List([α . β])
(define (->list m)
  (hash->list (repl->hash m)))

;; Hash(α, β) → (α ↦ β)
(define (<-hash h)
  (if (immutable-hash? h)
    (repl h)
    (error '<-hash "mutable: ~s" h)))

;; ... (values α β) ... → (α ↦ β)
(define-syntax (-for/map stx)
  (syntax-parse stx
    [(_ (~optional (~seq #:combine cod-⊔) #:defaults ([cod-⊔ #'(λ (v′ v) v)]))
        (clause ...) defs+exprs ...+)
     (with-syntax ([original stx])
       #'(for/fold/derived original ([m -∅]) (clause ...)
           (let-values ([(k v) (let () defs+exprs ...)])
             (-update m k (λ (v′) (cod-⊔ v′ v)) 'for/map-no-value))))]))

;; (α ↦ β) → Seq([α β])
(define (-in-map m)
  (in-hash (repl->hash m)))


(module+ test
  (require rackunit)
  (require (only-in "set.rkt" [-make set] [? set?]
                    [->list set->list] [<-list set<-list]))
  (require (only-in "match.rkt" match))

  (define r -∅)
  (check-equal? ((r 'x 1) 'x) 1)
  (check-equal? ((r 'x 1) 'y 2) ((r 'y 2) 'x 1))
  (check-equal? (-∈ 'x (r 'x 1)) #t)
  (check-equal? ('y . -∈ . (r 'x 1)) #f)
  (check-true
   (let ([l (for/list ([(k v) (-∈ ((r 'x 1) 'y 2))])
              (cons k v))])
     (not (not (and (member (cons 'y 2) l) (member (cons 'x 1) l))))))

  ;; (define pm (-make ['x (set 1 2 3)] ['y (set 2 4 5)]))
  ;; (match pm
  ;;   [(-make ['x (and s (set 1 t ...))] _ ...) t])
  )

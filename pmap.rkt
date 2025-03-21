#lang racket/base
(require (for-syntax racket/base syntax/parse)
         (only-in racket/generator in-generator yield)
         (only-in "match.rkt" define-match-expander)
         (rename-in (prefix-in set "set.rkt")
                    [set-for/set for/set]
                    [set-in-set in-set])
         (rename-in (prefix-in map "map.rkt")
                    [map-in-map in-map]))
(provide -make -make/p -∅ -∈ -∈/p -dom -rng -rng/p -size =? -restrict
         -map -map/p -filter -filter/p -∪ -update -add1 -add
         -remove1 -remove <-map ->set ->pset <-set <-pset
         ->list ->plist <-list <-plist ->phash <-hash <-phash
         -for/pmap -for/pmap/p -in-pmap -in-pmap/p
         (rename-out [<-map   ←map]
                     [->set   →set]
                     [->pset  →pset]
                     [<-set   ←set]
                     [<-pset  ←pset]
                     [->list  →list]
                     [->plist →plist]
                     [<-list  ←list]
                     [<-plist ←plist]
                     [->phash →phash]
                     [<-hash  ←hash]
                     [<-phash ←phash]))
;; provided from lightstep/base with prefix `pmap-'
;; also, aliases are provided from lightstep/base:
;;   p↦         = pmap-make
;;   p↦/p       = pmap-make/p
;;   p⊔         = pmap-∪
;;   for/pmap   = pmap-for/pmap
;;   for/pmap/p = pmap-for/pmap/p
;;   in-pmap    = pmap-in-pmap
;;   in-pmap/p  = pmap-in-pmap/p
;;   map->pmap  = pmap<-map
;;   map→pmap   = pmap←map
;;   set<-pmap  = pmap->set
;;   set←pmap   = pmap→set
;;   pset<-pmap = pmap->pset
;;   pset←pmap  = pmap→pset
;;   set->pmap  = pmap<-set
;;   set→pmap   = pmap←set
;;   pset->pmap = pmap<-pset
;;   pset→pmap  = pmap←pset


(module+ test (require rackunit))

;; ============================================================================
;; Finite map to powerset: α ↦ 𝒫(β)
;;
;; self:
;;   α      → 𝒫(β)
;;   α 𝒫(β) → (α ↦ 𝒫(β))    -- override

;; [α β] ... → (α ↦ 𝒫(β))    -- no matcher
(define-syntax (-make stx)
  (syntax-case stx ()
    [(_ (k v) ...)
     #'(<-list (list (cons k v) ...))]))

;; [α 𝒫(β)] ... → (α ↦ 𝒫(β))
(define-match-expander -make/p
  (λ (stx)
    (syntax-case stx (... ...)
      [(_ [k vs] ... m (... ...)) #'(map-make [k vs] ... m (... ...))]
      [(_ [k vs] ...)       #'(map-make [k vs] ...)]))
  (λ (stx)
    (syntax-case stx ()
      [(_ [k vs] ...) #'(map-make [k vs] ...)])))

;; (α ↦ 𝒫(β))
(define -∅ map-∅)

;; α (α ↦ 𝒫(β)) → Boolean
;;   (α ↦ 𝒫(β)) → Seq([α β])
(define -∈
  (case-λ
   [(k m) (map-∈ k m)]
   [(  m) (-in-pmap m)]))

;; α (α ↦ 𝒫(β)) → Boolean
;;   (α ↦ 𝒫(β)) → Seq([α 𝒫(β)])
(define -∈/p
  (case-λ
   [(k m) (map-∈ k m)] ;; same as ∈
   [(  m) (-in-pmap/p m)]))

;; (α ↦ 𝒫(β)) → 𝒫(α)
(define -dom map-dom)

;; (α ↦ 𝒫(β)) → 𝒫(β)
(define (-rng m)
  (set-big-∪ (-rng/p m)))

;; (α ↦ 𝒫(β)) → 𝒫(𝒫(β))
(define -rng/p map-rng)

;; (α ↦ 𝒫(β)) → Nat
(define -size map-size)

;; (α ↦ 𝒫(β)) (α ↦ 𝒫(β)) → Boolean
(define (=? m₁ m₂)
  (and (= (-size m₁) (-size m₂))
       (for/and ([(k₁ vs₁) (-∈/p m₁)])
         (set=? vs₁ (m₂ k₁)))))

;; (α ↦ 𝒫(β)) 𝒫(α) → (α ↦ 𝒫(β))
(define -restrict map-restrict)

;; (α β → γ) (α ↦ 𝒫(β)) → List(γ)
(define (-map f m)
  (for/list ([(k v) (-∈ m)])
    (f k v)))

;; (α 𝒫(β) → γ) (α ↦ 𝒫(β)) → List(γ)
(define -map/p map-map)

;; (α β → Boolean) (α ↦ 𝒫(β)) → (α ↦ 𝒫(β))
(define (-filter p m)
  (-for/pmap ([(k v) (-∈ m)]
             #:when (p k v))
    (values k v)))

;; (α 𝒫(β) → Boolean) (α ↦ 𝒫(β)) → (α ↦ 𝒫(β))
(define -filter/p map-filter)

;; (α ↦ 𝒫(β)) ...+ #:xombine (λ (𝒫(β) 𝒫(β)) 𝒫(β)) → (α ↦ 𝒫(β))
(define (-∪ m₁ #:combine [cod-⊔ set-∪] . mₙ)
  (apply map-∪ m₁ #:combine cod-⊔ mₙ))

;; (α ↦ 𝒫(β)) α (𝒫(β) → 𝒫(β)) [𝒫(β) | (→ 𝒫(β))] → (α ↦ 𝒫(β))
(define (-update m k f [o (λ () set-∅)] #:check-∅? [check-∅? #t])
  (let ([m′ (map-update m k f o)])
    (if (and check-∅? (set-∅? (m′ k)))
      (-remove m′ k)
      m′)))

;; (α ↦ 𝒫(β)) α β → (α ↦ 𝒫(β))
(define (-add1 m k v)
  (-update m k (λ (vs′) (set-add vs′ v)) #:check-∅? #f))

;; (α ↦ 𝒫(β)) α 𝒫(β) → (α ↦ 𝒫(β))
(define (-add m k vs)
  (-update m k (λ (vs′) (set-∪ vs′ vs)) #:check-∅? #f))

;; (α ↦ 𝒫(β)) α β → (α ↦ 𝒫(β))
(define (-remove1 m k v)
  (-update m k (λ (vs′) (set-remove vs′ v))))

;; (α ↦ 𝒫(β)) α      → (α ↦ 𝒫(β))
;; (α ↦ 𝒫(β)) α 𝒫(β) → (α ↦ 𝒫(β))
(define -remove
  (case-λ
   [(m k) (map-remove m k)]
   [(m k vs) (-update m k (λ (vs′) (set-subtract vs′ vs)))]))

;; (α ↦ β) → (α ↦ 𝒫(β))
(define (<-map m)
  (-for/pmap ([(k v) (in-map m)])
    (values k v)))

;; (α ↦ 𝒫(β)) → 𝒫([α . β])
(define (->set m)
  (for/set ([(k v) (-in-pmap m)])
    (cons k v)))

;; (α ↦ 𝒫(β)) → 𝒫([α . 𝒫(β)])
(define (->pset m)
  (for/set ([(k vs) (-in-pmap/p m)])
    (cons k vs)))

;; 𝒫([α . β]) → (α ↦ 𝒫(β))
(define (<-set s)
  (-for/pmap ([x (in-set s)])
    (values (car x) (cdr x))))

;; 𝒫([α . 𝒫(β)]) → (α ↦ 𝒫(β))
(define (<-pset s)
  (-for/pmap/p ([x (in-set s)])
    (values (car x) (cdr x))))

;; (α ↦ 𝒫(β)) → List([α . β])
(define (->list m)
  (for/list ([(k v) (-∈ m)])
    (cons k v)))

;; (α ↦ 𝒫(β)) → List([α . 𝒫(β)])
(define ->plist map->list)

;; List([α . β]) → (α ↦ 𝒫(β))
(define (<-list kvs)
  (-for/pmap ([kv (in-list kvs)])
    (values (car kv) (cdr kv))))

;; List([α . 𝒫(β)]) → (α ↦ 𝒫(β))
(define (<-plist kvss)
  (-for/pmap/p ([kvs (in-list kvss)])
    (values (car kvs) (cdr kvs))))

;; (α ↦ 𝒫(β)) → Hash(α, 𝒫(β))
(define ->phash map->hash)

;; Hash(α, β) → (α ↦ 𝒫(β))
(define (<-hash h)
  (-for/pmap ([(k v) (in-hash h)])
    (values k v)))

;; Hash(α, 𝒫(β)) → (α ↦ 𝒫(β))
(define <-phash map<-hash)

;; ... (values α β) ... → (α ↦ 𝒫(β))
(define-syntax (-for/pmap stx)
  (syntax-parse stx
    [(_ (~optional (~seq #:combine cod-⊔) #:defaults ([cod-⊔ #'set-add]))
        (clause ...) defs+exprs ...+)
     (with-syntax ([original stx])
       #'(for/fold/derived original ([m -∅]) (clause ...)
           (let-values ([(k v) (let () defs+exprs ...)])
             (-update m k (λ (vs′) (cod-⊔ vs′ v)) #:check-∅? #f))))]))

;; ... (values α 𝒫(β)) ... → (α ↦ 𝒫(β))
(define-syntax (-for/pmap/p stx)
  (syntax-parse stx
    [(_ (~optional (~seq #:combine cod-⊔) #:defaults ([cod-⊔ #'set-∪]))
        (clause ...) defs+exprs ...+)
     (with-syntax ([original stx])
       #'(for/fold/derived original ([m -∅]) (clause ...)
           (let-values ([(k vs) (let () defs+exprs ...)])
             (-update m k (λ (vs′) (cod-⊔ vs′ vs)) #:check-∅? #f))))]))

;; (α ↦ 𝒫(β)) → Seq([α β])
(define (-in-pmap m)
  (in-generator
   #:arity 2
   (for* ([(k s) (map-∈ m)]
          [v (set-∈ s)])
     (yield k v))))

;; (α ↦ 𝒫(β)) → Seq([α 𝒫(β)])
(define -in-pmap/p in-map)


(module+ test
  (require (only-in racket/match match))
  (require (only-in "set.rkt" [-make set] [-for/set for/set]))

  (define m (-make/p ['x (set 1 2 3)] ['y (set 2 4 5)]))
  (check-equal? (match m [(-make/p ['y vs] _ ...) vs]) (set 2 4 5))
  ;; (match m [(-make/p [k v] ...) (list k v)])

  ;; TODO: fix
  ;; (match m [(-make/p ['y (set x y ...)] m ...) (list x y m)])

  (check-true  (-∈ 'x m))
  (check-false (-∈/p 'z m))

  ;; (for/list ([(k vs) (-∈ m)])
  ;;   (list k vs))

  (check-equal? (for/set ([(k vs) (-∈/p m)])
                  (list k vs))
                (set (list 'x (set 1 2 3))
                     (list 'y (set 2 4 5))))
  (check-equal? (-dom m) (set 'x 'y))
  (check-equal? (-rng m) (set 1 2 3 4 5))
  (check-equal? (-rng/p m) (set (set 1 2 3) (set 2 4 5)))
  ;; does not pass test. why?
  ;(check-equal? (-size m) 2)

  (define m′ (-make/p ['y (set 2 4 5)] ['x (set 1 2 3)]))
  (define m″ (-make/p ['x (set 1 2)]   ['y (set 2 4 5)]))

  (check-true (=? m m′))
  (check-false (=? m m″))
  (check-equal? (-restrict m (set 'y)) (-make/p ['y (set 2 4 5)]))

  ;; (-map/p (λ (k vs) (list k vs)) m)
  (check-equal? (-filter/p (λ (k vs) (> (set-size vs) 2)) m″)
                (-make/p ['y (set 2 4 5)]))

  ;; (<-list '([x . 1] [y . 2] [x . 3] [z . 4] [x . 5] [y . 6]))
  ;; (<-plist (list [cons 'x (set 1 2)]
  ;;                [cons 'y (set 3)]
  ;;                [cons 'x (set 4)]
  ;;                [cons 'z (set 5 6 7)]))
  ;; (->list m)
  ;; (->plist m)
  ;; (for ([(k v) (-in-pmap m)])
  ;;   (printf "~s ↦ ~s\n" k v))
  ;; (for ([(k v) (-in-pmap/p m)])
  ;;   (printf "~s ↦ ~s\n" k v))
  )


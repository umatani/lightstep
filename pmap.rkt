#lang racket/base
(require (for-syntax racket/base syntax/parse)
         (only-in racket/match define-match-expander)
         (only-in racket/generator in-generator yield)
         (rename-in (prefix-in set "set.rkt")
                    [set-make set] [set-for/set for/set])
         (rename-in (prefix-in map "map.rkt")
                    [map-make map-↦] [map-in-map in-map]))
;; (provide -make -↦/p -∅ -∈ -∈/p -dom -rng -rng/p -size =? -restrict
;;          -map -map/p -filter -filter/p -∪ -update -add1 -add
;;          -remove1 -remove ->phash <-hash <-phash ->list ->plist
;;          <-list <-plist -for/pmap -for/pmap/p -in-pmap -in-pmap/p
;;          (rename-out [->phash →phash]
;;                      [<-hash  ←hash]
;;                      [<-phash ←phash]
;;                      [->list  →list]
;;                      [->plist →plist]
;;                      [<-list  ←list]
;;                      [<-plist ←plist]))

;; provided from lightstep/base with prefix `pmap-'
;; also, aliases are provided from lightstep/base:
;;   p↦         = pmap-make
;;   p↦/p       = pmap-↦/p
;;   p⊔         = pmap-∪
;;   for/pmap   = pmap-for/pmap
;;   for/pmap/p = pmap-for/pmap/p
;;   in-pmap    = pmap-in-pmap
;;   in-pmap/p  = pmap-in-pmap/p

(module+ test (require rackunit))

;; ============================================================================
;; Finite map to powerset: α ↦ 𝒫(β)
;;
;; self:
;;   α      → 𝒫(β)
;;   α 𝒫(β) → (α ↦ 𝒫(β))    -- override

;; [α β] ... → (α ↦ 𝒫(β))    -- no matcher
(define-syntax (↦ stx)
  (syntax-case stx ()
    [(_ (k v) ...)
     #'(list->pmap (list (cons k v) ...))]))

;; [α 𝒫(β)] ... → (α ↦ 𝒫(β))
(define-match-expander ↦p
  (λ (stx)
    (syntax-case stx (... ...)
      [(_ [k vs] (... ...)) #'(map-↦ [k vs] (... ...))]
      [(_ [k vs] ...)       #'(map-↦ [k vs] ...)]))
  (λ (stx)
    (syntax-case stx ()
      [(_ [k vs] ...) #'(↦ [k vs] ...)])))

;; (α ↦ 𝒫(β))
(define ∅ map-∅)

;; α (α ↦ 𝒫(β)) → Boolean
;;   (α ↦ 𝒫(β)) → Seq([α β])
(define ∈
  (case-λ
   [(k m) (map-∈ k m)]
   [(  m) (in-pmap m)]))

;; α (α ↦ 𝒫(β)) → Boolean
;;   (α ↦ 𝒫(β)) → Seq([α 𝒫(β)])
(define ∈p
  (case-λ
   [(k m) (map-∈ k m)] ;; same as ∈
   [(  m) (in-pmap/p m)]))

;; (α ↦ 𝒫(β)) → 𝒫(α)
(define dom map-dom)

;; (α ↦ 𝒫(β)) → 𝒫(β)
(define (rng m)
  (apply set-∪ (set→list (rng/p m))))

;; (α ↦ 𝒫(β)) → 𝒫(𝒫(β))
(define rng/p map-rng)

;; (α ↦ 𝒫(β)) → Nat
(define size map-size)

;; (α ↦ 𝒫(β)) (α ↦ 𝒫(β)) → Boolean
(define (pmap=? m₁ m₂)
  (and (= (size m₁) (size m₂))
       (for/and ([(k₁ vs₁) (∈p m₁)])
         (set=? vs₁ (m₂ k₁)))))

;; (α ↦ 𝒫(β)) 𝒫(α) → (α ↦ 𝒫(β))
(define restrict map-restrict)

;; (α β → γ) (α ↦ 𝒫(β)) → List(γ)
(define (pmap-map f m)
  (for/list ([(k v) (∈ m)])
    (f k v)))

;; (α 𝒫(β) → γ) (α ↦ 𝒫(β)) → List(γ)
(define pmap-map/p map-map)

;; (α β → Boolean) (α ↦ 𝒫(β)) → (α ↦ 𝒫(β))
(define (pmap-filter p m)
  (for/pmap ([(k v) (∈ m)]
             #:when (p k v))
    (values k v)))

;; (α 𝒫(β) → Boolean) (α ↦ 𝒫(β)) → (α ↦ 𝒫(β))
(define pmap-filter/p map-filter)

;; (α ↦ 𝒫(β)) ...+ #:xombine (λ (𝒫(β) 𝒫(β)) 𝒫(β)) → (α ↦ 𝒫(β))
(define (⊔ m₁ #:combine [cod-⊔ set-∪] . mₙ)
  (apply map-∪ m₁ #:combine cod-⊔ mₙ))

;; (α ↦ 𝒫(β)) α (𝒫(β) → 𝒫(β)) [𝒫(β) | (→ 𝒫(β))] → (α ↦ 𝒫(β))
(define (pmap-update m k f [o (λ () set-∅)])
  (map-update m k f o))

;; (α ↦ 𝒫(β)) α β → (α ↦ 𝒫(β))
(define (pmap-add1 m k v)
  (pmap-update m k (λ (vs′) (set-add vs′ v))))

;; (α ↦ 𝒫(β)) α 𝒫(β) → (α ↦ 𝒫(β))
(define (pmap-add m k vs)
  (pmap-update m k (λ (vs′) (set-∪ vs′ vs))))

;; TODO: empty-check
;; (α ↦ 𝒫(β)) α β → (α ↦ 𝒫(β))
(define (pmap-remove1 m k v)
  (pmap-update m k (λ (vs′) (set-remove vs′ v))))

;; TODO: empty-check
;; (α ↦ 𝒫(β)) α      → (α ↦ 𝒫(β))
;; (α ↦ 𝒫(β)) α 𝒫(β) → (α ↦ 𝒫(β))
(define pmap-remove
  (case-λ
   [(m k) (map-remove m k)]
   [(m k vs) (pmap-update m k (λ (vs′) (set-subtract vs′ vs)))]))

;; (α ↦ 𝒫(β)) → Hash(α, 𝒫(β))
(define pmap->phash map->hash)

;; Hash(α, β) (α ↦ 𝒫(β))
(define (hash->pmap h)
  (for/pmap ([(k v) (in-hash h)])
    (values k v)))

;; Hash(α, 𝒫(β)) (α ↦ 𝒫(β))
(define phash->pmap map<-hash)

;; (α ↦ 𝒫(β)) → List([α . β])
(define (pmap->list m)
  (for/list ([(k v) (∈ m)])
    (cons k v)))

;; (α ↦ 𝒫(β)) → List([α . 𝒫(β)])
(define pmap->plist map->list)

;; List([α . β]) → (α ↦ 𝒫(β))
(define (list->pmap kvs)
  (for/pmap ([kv (in-list kvs)])
    (values (car kv) (cdr kv))))

;; List([α . 𝒫(β)]) → (α ↦ 𝒫(β))
(define (plist->pmap kvss)
  (for/pmap/p ([kvs (in-list kvss)])
    (values (car kvs) (cdr kvs))))

;; ... (values α β) ... → (α ↦ 𝒫(β))
(define-syntax (for/pmap stx)
  (syntax-parse stx
    [(_ (~optional (~seq #:combine cod-⊔) #:defaults ([cod-⊔ #'set-add]))
        (clause ...) defs+exprs ...+)
     (with-syntax ([original stx])
       #'(for/fold/derived original ([m ∅]) (clause ...)
           (let-values ([(k v) (let () defs+exprs ...)])
             (pmap-update m k (λ (vs′) (cod-⊔ vs′ v))))))]))

;; ... (values α 𝒫(β)) ... → (α ↦ 𝒫(β))
(define-syntax (for/pmap/p stx)
  (syntax-parse stx
    [(_ (~optional (~seq #:combine cod-⊔) #:defaults ([cod-⊔ #'set-∪]))
        (clause ...) defs+exprs ...+)
     (with-syntax ([original stx])
       #'(for/fold/derived original ([m ∅]) (clause ...)
           (let-values ([(k vs) (let () defs+exprs ...)])
             (pmap-update m k (λ (vs′) (cod-⊔ vs′ vs))))))]))

;; (α ↦ 𝒫(β)) → Seq([α β])
(define (in-pmap m)
  (in-generator
   #:arity 2
   (for* ([(k s) (map-∈ m)]
          [v (set-∈ s)])
     (yield k v))))

;; (α ↦ 𝒫(β)) → Seq([α 𝒫(β)])
(define in-pmap/p in-map)


;; (module+ test
;;   (require (only-in racket/match match))

;;   (define m (↦p ['x (set 1 2 3)] ['y (set 2 4 5)]))
;;   (check-equal? (match m [(↦p ['y vs]) vs]) (set 2 4 5))
;;   ;; (match m [(↦p [k v] ...) (list k v)])

;;   (check-true  (∈ 'x m))
;;   (check-false (∈p 'z m))

;;   ;; (for/list ([(k vs) (∈ m)])
;;   ;;   (list k vs))

;;   (check-equal? (for/set ([(k vs) (∈p m)])
;;                   (list k vs))
;;                 (set (list 'x (set 1 2 3))
;;                      (list 'y (set 2 4 5))))
;;   (check-equal? (dom m) (set 'x 'y))
;;   (check-equal? (rng m) (set 1 2 3 4 5))
;;   (check-equal? (rng/p m) (set (set 1 2 3) (set 2 4 5)))
;;   ;; does not pass test. why?
;;   ;(check-equal? (size m) 2)

;;   (define m′ (↦p ['y (set 2 4 5)] ['x (set 1 2 3)]))
;;   (define m″ (↦p ['x (set 1 2)]   ['y (set 2 4 5)]))

;;   (check-true (pmap=? m m′))
;;   (check-false (pmap=? m m″))
;;   (check-equal? (restrict m (set 'y)) (↦p ['y (set 2 4 5)]))

;;   ;; (pmap-map/p (λ (k vs) (list k vs)) m)
;;   (check-equal? (pmap-filter/p (λ (k vs) (> (set-size vs) 2)) m″)
;;                 (↦p ['y (set 2 4 5)]))

;;   ;; (list->pmap '([x . 1] [y . 2] [x . 3] [z . 4] [x . 5] [y . 6]))
;;   ;; (plist->pmap (list [cons 'x (set 1 2)]
;;   ;;                    [cons 'y (set 3)]
;;   ;;                    [cons 'x (set 4)]
;;   ;;                    [cons 'z (set 5 6 7)]))
;;   ;; (pmap->list m)
;;   ;; (pmap->plist m)
;;   ;; (for ([(k v) (in-pmap m)])
;;   ;;   (printf "~s ↦ ~s\n" k v))

;;   ;; (for ([(k v) (in-pmap/p m)])
;;   ;;   (printf "~s ↦ ~s\n" k v))
;;   )


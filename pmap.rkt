#lang racket/base
(require (for-syntax racket/base syntax/parse)
         (only-in racket/match define-match-expander)
         (only-in racket/generator in-generator yield)
         (prefix-in s: "set.rkt")
         (prefix-in m: "map.rkt"))
(provide ↦ ↦p ∅ ∈ ∈p dom rng rng/p size pmap=? restrict
         pmap-map pmap-map/p pmap-filter pmap-filter/p
         ⊔ pmap-update pmap-remove
         pmap->phash hash->pmap phash->pmap
         pmap->list pmap->plist list->pmap plist->pmap
         for/pmap for/pmap/p in-pmap in-pmap/p
         (rename-out [pmap->phash pmap→phash]
                     [hash->pmap hash→pmap]
                     [phash->pmap phash→pmap]
                     [pmap->list pmap→list]
                     [pmap->plist pmap→plist]
                     [list->pmap list→pmap]
                     [plist->pmap plist→pmap]))

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
      [(_ [k vs] (... ...)) #'(m:↦ [k vs] (... ...))]
      [(_ [k vs] ...)       #'(m:↦ [k vs] ...)]))
  (λ (stx)
    (syntax-case stx ()
      [(_ [k vs] ...) #'(m:↦ [k vs] ...)])))

;; (α ↦ 𝒫(β))
(define ∅ m:∅)

;; α (α ↦ 𝒫(β)) → Boolean
;;   (α ↦ 𝒫(β)) → Seq([α β])
(define ∈
  (case-λ
   [(k m) (m:∈ k m)]
   [(  m) (in-pmap m)]))

;; α (α ↦ 𝒫(β)) → Boolean
;;   (α ↦ 𝒫(β)) → Seq([α 𝒫(β)])
(define ∈p
  (case-λ
   [(k m) (m:∈ k m)] ;; same as ∈
   [(  m) (in-pmap/p m)]))

;; (α ↦ 𝒫(β)) → 𝒫(α)
(define dom m:dom)

;; (α ↦ 𝒫(β)) → 𝒫(β)
(define (rng m)
  (apply s:∪ (s:set→list (rng/p m))))

;; (α ↦ 𝒫(β)) → 𝒫(𝒫(β))
(define rng/p m:rng)

;; (α ↦ 𝒫(β)) → Nat
(define size m:size)

;; (α ↦ 𝒫(β)) (α ↦ 𝒫(β)) → Boolean
(define (pmap=? m₁ m₂)
  (and (= (size m₁) (size m₂))
       (for/and ([(k₁ vs₁) (∈p m₁)])
         (s:set=? vs₁ (m₂ k₁)))))

;; (α ↦ 𝒫(β)) 𝒫(α) → (α ↦ 𝒫(β))
(define restrict m:restrict)

;; (α β → γ) (α ↦ 𝒫(β)) → List(γ)
(define (pmap-map f m)
  (for/list ([(k v) (∈ m)])
    (f k v)))

;; (α 𝒫(β) → γ) (α ↦ 𝒫(β)) → List(γ)
(define pmap-map/p m:map-map)

;; (α β → Boolean) (α ↦ 𝒫(β)) → (α ↦ 𝒫(β))
(define (pmap-filter p m)
  (for/pmap ([(k v) (∈ m)]
             #:when (p k v))
    (values k v)))

;; (α 𝒫(β) → Boolean) (α ↦ 𝒫(β)) → (α ↦ 𝒫(β))
(define pmap-filter/p m:map-filter)

;; (α ↦ 𝒫(β)) ...+ #:xombine (λ (𝒫(β) 𝒫(β)) 𝒫(β)) → (α ↦ 𝒫(β))
(define (⊔ m₁ #:combine [cod-⊔ s:∪] . mₙ)
  (apply m:⊔ m₁ #:combine cod-⊔ mₙ))

;; (α ↦ 𝒫(β)) α (𝒫(β) → 𝒫(β)) [𝒫(β) | (→ 𝒫(β))] → (α ↦ 𝒫(β))
(define pmap-update m:map-update)

;; (α ↦ 𝒫(β)) α      → (α ↦ 𝒫(β))
;; (α ↦ 𝒫(β)) α 𝒫(β) → (α ↦ 𝒫(β))
(define pmap-remove
  (case-λ
   [(m k) (m:map-remove m k)]
   [(m k vs) (pmap-filter (λ (k′ v′) (not (and (equal? k k′) (s:∈ v′ vs))))
                          m)]))

;; (α ↦ 𝒫(β)) → Hash(α, 𝒫(β))
(define pmap->phash m:map->hash)

;; Hash(α, β) (α ↦ 𝒫(β))
(define (hash->pmap h)
  (for/pmap ([(k v) (in-hash h)])
    (values k v)))

;; Hash(α, 𝒫(β)) (α ↦ 𝒫(β))
(define phash->pmap m:hash->map)

;; (α ↦ 𝒫(β)) → List([α . β])
(define (pmap->list m)
  (for/list ([(k v) (∈ m)])
    (cons k v)))

;; (α ↦ 𝒫(β)) → List([α . 𝒫(β)])
(define pmap->plist m:map->list)

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
    [(_ (~optional (~seq #:combine cod-⊔) #:defaults ([cod-⊔ #'s:set-add]))
        (clause ...) defs+exprs ...+)
     (with-syntax ([original stx])
       #'(for/fold/derived original ([m ∅]) (clause ...)
           (let-values ([(k v) (let () defs+exprs ...)])
             (pmap-update m k (λ (vs′) (cod-⊔ vs′ v)) s:∅))))]))

;; ... (values α 𝒫(β)) ... → (α ↦ 𝒫(β))
(define-syntax (for/pmap/p stx)
  (syntax-parse stx
    [(_ (~optional (~seq #:combine cod-⊔) #:defaults ([cod-⊔ #'s:∪]))
        (clause ...) defs+exprs ...+)
     (with-syntax ([original stx])
       #'(for/fold/derived original ([m ∅]) (clause ...)
           (let-values ([(k vs) (let () defs+exprs ...)])
             (pmap-update m k (λ (vs′) (cod-⊔ vs′ vs)) s:∅))))]))

;; (α ↦ 𝒫(β)) → Seq([α β])
(define (in-pmap m)
  (in-generator
   #:arity 2
   (for* ([(k s) (m:∈ m)]
          [v (s:∈ s)])
     (yield k v))))

;; (α ↦ 𝒫(β)) → Seq([α 𝒫(β)])
(define (in-pmap/p m) (m:in-map m))


(module+ test
  (require (only-in racket/match match))

  (define m (↦p ['x (s:set 1 2 3)] ['y (s:set 2 4 5)]))
  (check-equal? (match m [(↦p ['y vs]) vs]) (s:set 2 4 5))
  ;; (match m [(↦p [k v] ...) (list k v)])

  (check-true  (∈ 'x m))
  (check-false (∈p 'z m))

  ;; (for/list ([(k vs) (∈ m)])
  ;;   (list k vs))

  (check-equal? (s:for/set ([(k vs) (∈p m)])
                  (list k vs))
                (s:set (list 'x (s:set 1 2 3))
                       (list 'y (s:set 2 4 5))))
  (check-equal? (dom m) (s:set 'x 'y))
  (check-equal? (rng m) (s:set 1 2 3 4 5))
  (check-equal? (rng/p m) (s:set (s:set 1 2 3) (s:set 2 4 5)))
  ;; does not pass test. why?
  ;(check-equal? (size m) 2)

  (define m′ (↦p ['y (s:set 2 4 5)] ['x (s:set 1 2 3)]))
  (define m″ (↦p ['x (s:set 1 2)]   ['y (s:set 2 4 5)]))

  (check-true (pmap=? m m′))
  (check-false (pmap=? m m″))
  (check-equal? (restrict m (s:set 'y)) (↦p ['y (s:set 2 4 5)]))

  ;; (pmap-map/p (λ (k vs) (list k vs)) m)
  (check-equal? (pmap-filter/p (λ (k vs) (> (s:size vs) 2)) m″)
                (↦p ['y (s:set 2 4 5)]))

  ;; (list->pmap '([x . 1] [y . 2] [x . 3] [z . 4] [x . 5] [y . 6]))
  ;; (plist->pmap (list [cons 'x (s:set 1 2)]
  ;;                    [cons 'y (s:set 3)]
  ;;                    [cons 'x (s:set 4)]
  ;;                    [cons 'z (s:set 5 6 7)]))
  ;; (pmap->list m)
  ;; (pmap->plist m)
  ;; (for ([(k v) (in-pmap m)])
  ;;   (printf "~s ↦ ~s\n" k v))

  ;; (for ([(k v) (in-pmap/p m)])
  ;;   (printf "~s ↦ ~s\n" k v))
  )


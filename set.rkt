#lang racket/base
(require (for-syntax racket/base syntax/parse)
         (prefix-in r: racket/set)
         (only-in racket/match define-match-expander))
(provide -make (rename-out [set? ?]) -∅ -∅? -∈ -size =? -⊆ -∪
         -add -remove -subtract -map -filter ->list <-list -for/set -in-set
         (rename-out [->list →list]
                     [<-list ←list]))
;; provided from lightstep/base with prefix `set-'
;; also, aliases are provided from lightstep/base:
;;   set     = set-make
;;   ∅       = set-∅
;;   ∅?      = set-∅?
;;   ∈       = set-∈
;;   ∪       = set-∪
;;   ⊆       = set-⊆
;;   for/set = set-for/set
;;   in-set  = set-in-set


;; ============================================================================
;; Finite set: 𝒫(α)

;; α → Boolean
(struct repl (elems)
  #:transparent  ;; for equal?
  #:property prop:sequence
  (λ (s) (-in-set s))
  #:property
  prop:procedure
  (λ (s x) (-∈ x s))
  #:methods gen:custom-write
  [(define (write-proc s port mode)
     (when mode (write-string "{" port))
     (let ([es (repl-elems s)]
           [recur (case mode
                    [(#t) write]
                    [(#f) display]
                    [else (lambda (p port) (print p port mode))])])
       (unless (zero? (r:set-count es))
         (recur (r:set-first es) port)
         (for-each (λ (e)
                     (write-string " " port)
                     (recur e port))
                   (r:set->list (r:set-rest es)))))
     (when mode (write-string "}" port)))])

;; α ... → 𝒫(α)
(define-match-expander -make
  (syntax-rules (... ...)
    [(-make p ... q (... ...))
     (? set? (app (compose1 r:set->list repl-elems)
                  (list-no-order p ... q (... ...))))]
    [(-make p ...)
     (? set? (app (compose1 r:set->list repl-elems)
                  (list-no-order p ...)))])
  (syntax-id-rules (-make)
    [(-make p ...) (repl (r:set p ...))]
    [-make (λ args (repl (apply r:set args)))]))

;; Any → Boolean
(define set? repl?)

;; 𝒫(α)
(define -∅ (-make))

;; 𝒫(α) → Boolean
(define (-∅? s)
  (r:set-empty? (repl-elems s)))

;; α 𝒫(α) → Boolean
;;   𝒫(α) → Seq(α)
(define -∈
  (case-λ
   [(e s) (r:set-member? (repl-elems s) e)]
   [(  s) (-in-set s)]))

;; 𝒫(α) → Nat
(define (-size s)
  (r:set-count (repl-elems s)))

;; 𝒫(α) 𝒫(α) → Boolean
(define (=? s s′)
  (r:set=? (repl-elems s) (repl-elems s′)))

;; 𝒫(α) 𝒫(α) → 𝒫(α)
(define (-⊆ s s′)
  (r:subset? (repl-elems s) (repl-elems s′)))

;; 𝒫(α) ... → 𝒫(α)
(define (-∪ . ss)
  (if (null? ss)
    -∅
    (repl (apply r:set-union (map repl-elems ss)))))

;; 𝒫(α) α → 𝒫(α)
(define (-add s e)
  (repl (r:set-add (repl-elems s) e)))

;; 𝒫(α) α → 𝒫(α)
(define (-remove s e)
  (repl (r:set-remove (repl-elems s) e)))

;; 𝒫(α) ... → 𝒫(α)
(define (-subtract . ss)
  (repl (apply r:set-subtract (map repl-elems ss))))

;; (α → β) 𝒫(α) → List(β)
(define (-map f s)
  (r:set-map (repl-elems s) f))

;; (α → Boolean) 𝒫(α) → 𝒫(α)
(define (-filter p s)
  (-for/set ([x (-∈ s)]
             #:when (p x))
    x))

;; 𝒫(α) → List(α)
(define (->list s)
  (r:set->list (repl-elems s)))

;; List(α) → 𝒫(α)
(define (<-list l)
  (repl (r:list->set l)))

;; ... α ... → 𝒫(α)
(define-syntax (-for/set stx)
  (syntax-parse stx
    [(_ clauses defs+exprs ...+)
     (with-syntax ([original stx])
       #'(for/fold/derived original ([s -∅]) clauses
           (let ([v (let () defs+exprs ...)])
             (-add s v))))]))

;; 𝒫(α) → Seq(α)
(define (-in-set s)
  (r:in-set (repl-elems s)))


(module+ test
  (require (only-in "match.rkt" match))

  (define s (-make 1 2 3))
  (match s
    [(-make a b c) (list a b c)])
  )

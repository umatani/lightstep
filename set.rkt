#lang racket/base
(require (for-syntax racket/base syntax/parse)
         (prefix-in r: racket/set)
         (only-in racket/match define-match-expander))
(provide set set? ∅ ∅? ∈ size set=? ∪ set-add set-remove set-subtract ⊆
         set-map set-filter set->list list->set for/set in-set
         (rename-out [set->list set→list]
                     [list->set list→set]))

;; ============================================================================
;; Finite set: 𝒫(α)

(struct repl (elems)
  #:transparent  ;; for equal?
  #:property prop:sequence
  (lambda (s) (in-set s))
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
(define-match-expander set
  (syntax-rules (... ...)
    [(set p ... q (... ...))
     (? set? (app (compose1 r:set->list repl-elems)
                  (list-no-order p ... q (... ...))))]
    [(set p ...)
     (? set? (app (compose1 r:set->list repl-elems)
                  (list-no-order p ...)))])
  (syntax-id-rules (set)
    [(set p ...) (repl (r:set p ...))]
    [set (λ args (repl (apply r:set args)))]))

;; Any → Boolean
(define set? repl?)

;; 𝒫(α)
(define ∅ (set))

;; 𝒫(α) → Boolean
(define (∅? s)
  (r:set-empty? (repl-elems s)))

;; α 𝒫(α) → Boolean
;;   𝒫(α) → Seq(α)
(define ∈
  (case-λ
   [(e s) (r:set-member? (repl-elems s) e)]
   [(  s) (in-set s)]))

;; 𝒫(α) → Nat
(define (size s)
  (r:set-count (repl-elems s)))

;; 𝒫(α) 𝒫(α) → Boolean
(define (set=? s s′)
  (r:set=? (repl-elems s) (repl-elems s′)))

;; 𝒫(α) ... → 𝒫(α)
(define (∪ . ss)
  (if (null? ss)
    ∅
    (repl (apply r:set-union (map repl-elems ss)))))

;; 𝒫(α) α → 𝒫(α)
(define (set-add s e)
  (repl (r:set-add (repl-elems s) e)))

;; 𝒫(α) α → 𝒫(α)
(define (set-remove s e)
  (repl (r:set-remove (repl-elems s) e)))

;; 𝒫(α) ... → 𝒫(α)
(define (set-subtract . ss)
  (repl (apply r:set-subtract (map repl-elems ss))))

;; 𝒫(α) 𝒫(α) → 𝒫(α)
(define (⊆ s s′)
  (r:subset? (repl-elems s) (repl-elems s′)))

;; (α → β) 𝒫(α) → List(β)
(define (set-map f s)
  (r:set-map (repl-elems s) f))

;; (α → Boolean) 𝒫(α) → 𝒫(α)
(define (set-filter p s)
  (for/set ([x (∈ s)]
            #:when (p x))
    x))

;; 𝒫(α) → List(α)
(define (set->list s)
  (r:set->list (repl-elems s)))

;; List(α) → 𝒫(α)
(define (list->set l)
  (repl (r:list->set l)))

;; ... α ... → 𝒫(α)
(define-syntax (for/set stx)
  (syntax-parse stx
    [(_ clauses defs+exprs ...+)
     (with-syntax ([original stx])
       #'(for/fold/derived original ([s ∅]) clauses
           (let ([v (let () defs+exprs ...)])
             (set-add s v))))]))

;; 𝒫(α) → Seq(α)
(define (in-set s)
  (r:in-set (repl-elems s)))



(module+ test
  (require (only-in "match.rkt" match))

  (define s (set 1 2 3))
  (match s
    [(set a b c) (list a b c)])
  )

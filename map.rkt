#lang racket/base
(require (for-syntax racket/base)
         (only-in racket/match define-match-expander)
         (only-in racket/hash hash-union)
         (only-in "set.rkt" for/set [∈ s:∈]))
(provide ↦ map? ∅ ∈ ⊔ size map->list hash->map
         keys rng restrict map-remove for/map in-map
         (rename-out [repl->hash map->hash]
                     [repl->hash map→hash]
                     [map->list map→list]
                     [hash->map hash→map]))

;; ============================================================================
;; Finite map data structure

(struct repl (>hash)
  #:transparent  ;; for equal?
  #:property
  prop:procedure
  (case-λ
    [(m x) 
     (if (∈ x m)
       (hash-ref (repl->hash m) x)
       (error 'map "has no value for key: ~a" x))]
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

(define-match-expander ↦
  (λ (stx)
    (syntax-case stx ()
      [(_ (x y) ...)
       #'(? map? (app repl->hash (hash-table (x y) ...)))]))
  (λ (stx)
    (syntax-case stx ()
      [(_ (x y) ...)
       #'(repl (make-immutable-hash (list (cons x y) ...)))])))

(define map? repl?)

(define ∅ (↦))

(define hash->map repl)

(define (map->list m)
  (hash->list (repl->hash m)))

(define ∈
  (case-λ
   [(k m) (hash-has-key? (repl->hash m) k)]
   [(m)   (in-map m)]))
    
(define (keys m)
  (for/set ([(k _) (∈ m)]) k))

(define (rng m)
  (for/set ([(_ v) (∈ m)]) v))

(define (restrict m xs)
  (for/map ([(x _) (∈ m)]
            #:when (s:∈ x xs))
    (values x (m x))))

(define (size m)
  (hash-count (repl->hash m)))

(define (map-remove m k)
  (hash->map (hash-remove (repl->hash m) k)))

(define (⊔ m₁ #:combine [cod-⊔ (λ (x _) x)] . mₙ)
  (repl (apply hash-union
               (repl->hash m₁)
               (foldl (λ (m a) (cons (repl->hash m) a)) '() mₙ)
               #:combine cod-⊔)))

(define-syntax (for/map stx)
  (syntax-case stx ()
    [(_ clauses defs+exprs ...)
     (with-syntax ([original stx])
       #'(for/fold/derived original ([m ∅]) clauses
           (let-values ([(k v) (let () defs+exprs ...)])
             (m k v))))]))

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

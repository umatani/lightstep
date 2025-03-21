#lang racket
(require (for-syntax racket/base syntax/parse)
         "main.rkt")
(provide (except-out (all-from-out racket) λ #%app define)
         (rename-out [c.app #%app] [c.λ λ] [c.define define])
         (all-from-out "main.rkt"))


(define-syntax (c.λ stx)
  (syntax-parse stx
    [(_ ()   e ...+) #'(λ () e ...)]
    [(_ (p) e ...+) #'(match-λ [p (begin e ...)])]
    [(_ (p₀ p ...+) e ...+) #'(match-λ [p₀ (c.λ (p ...) e ...)])]))

(define-syntax (c.app stx)
  (syntax-parse stx
    [(_ f:expr) #'(#%app f)]
    [(_ f:expr e:expr) #'(#%app f e)]
    [(_ f:expr e₀:expr e:expr ...+)
     #'(c.app (#%app f e₀) e ...)]))

(define-syntax (c.define stx)
  (syntax-parse stx
    [(_ x:id e:expr) #'(define x e)]
    [(_ (f:id p ...) e ...) #'(define f (c.λ (p ...) e ...))]))


;; TODO: curried converter
(define (curried f) f)

(module+ test
  (define f0 (c.λ () 'void))
  (c.app f0)
  (define f1 (c.λ (x) x))
  (c.app f1 1)
  (define f2 (c.λ (x y) (+ x y)))
  (c.app f2 100 200)
  (define g2 (c.app f2 100))
  (c.app g2 200)


  ;; #lang s-exp lightstep/curried
  ;; (require (prefix-in r: racket))

  ;; ;; (define (lhs f g e)
  ;; ;;   (compose1 (λ (xs) (foldr f e xs))
  ;; ;;             (λ (xs) (map g xs))))
  ;; ;; (define (rhs f g e)
  ;; ;;   (λ (xs) (foldr ;(λ (x e) (f (g x) e))
  ;; ;;                  (compose f (λ (x e) (values (g x) e)))
  ;; ;;                  e xs)))

  ;; ;; ((lhs cons add1 '()) '(1 2 3 4 5))
  ;; ;; ((rhs cons add1 '()) '(1 2 3 4 5))

  ;; (define cons (λ (x y) (r:#%app r:cons x y)))
  ;; (procedure-arity r:cons)
  ;; (define + (λ (x y) (r:#%app r:+ x y)))
  ;; (procedure-arity r:+)
  ;; (define compose1 (λ (f g) (r:#%app r:compose1 f g)))
  ;; (procedure-arity r:compose1)
  ;; (define map (λ (f x) (r:#%app r:map f x)))
  ;; (procedure-arity r:map)
  ;; ;(define foldr (λ (f e xs) (r:#%app r:foldr f e xs)))
  ;; (procedure-arity r:foldr)
  ;; (define foldr (λ (f e xs)
  ;;                 (match xs
  ;;                   ['() e]
  ;;                   [`(,x ,xs′ ...) (f x (foldr f e xs′))])))
  ;; (procedure-arity r:foldr)

  ;; (define f0 (λ () 'void))
  ;; (f0)
  ;; (define f1 (λ (x) x))
  ;; (f1 1)
  ;; (define f2 (λ (x y) (+ x y)))
  ;; ((f2 100) 200)

  ;; (define lhs (λ (f g e) (compose1 (foldr f e) (map g))))
  ;; (define rhs (λ (f g e) (foldr (compose1 f g) e)))
  ;; (lhs cons add1 '() '(1 2 3 4 5))
  ;; (rhs cons add1 '() '(1 2 3 4 5))
  )

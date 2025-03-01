#lang racket/base
(require (only-in "transformers.rkt" define-monad)
         (only-in "reduction.rkt" ReduceM))
(provide mapM sequence)

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

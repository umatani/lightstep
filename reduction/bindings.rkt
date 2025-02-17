#lang racket
(require "../transformers.rkt")
(provide ReduceT
         return bind do for/monad+ ask local tell hijack get put fail try
         mzero mplus mconcat monoid-functor)

(define (ReduceT M) (FailT (NondetT M)))
(define-monad (ReduceT ID))


#lang racket/base
(require lightstep/base
         (for-syntax racket/base syntax/parse)
         (only-in lightstep/transformers define-monad)
         (prefix-in r: (only-in racket/set mutable-set set-member? set-add!)))
(provide match? mmap mmap-lookup mmap-lookup? mmap-ext1 mmap-ext reachable?)

(module+ test (require rackunit))

;;=============================================================================
;; Utils

(define-syntax (match? stx)
  (syntax-parse stx
    [(_ p x)
     #'(match x
         [p #t]
         [_ #f])]))

;; multi-map: A → 𝒫(B)

(define (mmap . bs)
  (match bs
    [`([,xs ,ts] ...)
     (for/fold ([m map-∅])
               ([x xs]
                [t ts])
       (m x (∪ (if (map-∈ x m)
                 (m x)
                 ∅)
               (set t))))]))

(define (mmap-lookup m x)
  (match m
    [(↦ [x ts]) ts]
    [_ ∅]))

(define (mmap-lookup? m x t)
  (∈ t (mmap-lookup m x)))

(module+ test
  (check-true  (mmap-lookup? (mmap '[x 1] '[y 2] '[x 3]) 'x 1))
  (check-false (mmap-lookup? (mmap '[x 1] '[y 2] '[x 3]) 'x 2))
  (check-true  (mmap-lookup? (mmap '[x 1] '[y 2] '[x 3]) 'x 3))
  (check-equal? (mmap-lookup (mmap '[x 1] '[y 2] '[x 3]) 'x) (set 1 3)))

(define (mmap-ext1 m x t)
  (match m
    [(↦ [x (set)])   (m x (set t))]
    [(↦ [x (set _)]) (m x (set t))]
    [(↦ [x (set _ _ ...)])
     (error 'mmap-ext1 "multiple bindings of ~s in ~s" x m)]
    [(↦) (m x (set t))]))

(define (mmap-ext m . bs)
  (match bs
    ['() m]
    [`([,x ,t] ,@bs′) (mmap-ext1 (apply mmap-ext m bs′) x t)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; reachable? (useless)

(struct Queueof (head tail) #:transparent #:mutable
  #:constructor-name Queue)

(define (make-queue) (Queue '() '()))

(define (queue-empty? q)
  (and (null? (Queueof-head q)) (null? (Queueof-tail q))))

(define (enqueue! q a)
  (set-Queueof-tail! q (cons a (Queueof-tail q))))

(define (dequeue! q)
  (when (queue-empty? q)
    (error 'dequeue! "queue is empty"))
  (when (null? (Queueof-head q))
    (set-Queueof-head! q (reverse (Queueof-tail q)))
    (set-Queueof-tail! q '()))
  (begin0
      (car (Queueof-head q))
    (set-Queueof-head! q (cdr (Queueof-head q)))))

(define (reachable? → ς-init ς-final)
  (define wl (make-queue))
  (define Σ (r:mutable-set))

  (define (search)
    (if (r:set-member? Σ ς-final)
      #t
      (if (queue-empty? wl)
        #f
        (begin
          (for ([ς′ (in-set (→ (dequeue! wl)))]
                #:unless (r:set-member? Σ ς′))
            (enqueue! wl ς′)
            (r:set-add! Σ ς′))
          (search)))))
  (enqueue! wl ς-init)
  (r:set-add! Σ ς-init)
  (search))

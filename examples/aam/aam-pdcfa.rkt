#lang racket
(require lightstep/base lightstep/transformers)

(module+ test (require rackunit))

;; Abstracting Abstract Machines from:
;;   https://dvanhorn.github.io/redex-aam-tutorial/

;; Continuation を Abstracting Abstract Control 版に．
;; PCFσ*ではなく，KがメタスタックのままのPCFσベースの方が適切(？)

(module+ test
  ;; 2 ReaderT, 4 StateT, and 1 NondetT
  ;; both combinations can work in a uniform manner
  
  ;; (define-monad (ReaderT                      ; r₂ (env)
  ;;                (ReaderT                     ; r₁ (ξ)
  ;;                 (StateT                     ; s₃ (store)
  ;;                  #f (StateT                 ; s₂ (σ)
  ;;                      #f
  ;;                      (StateT            ; s₁ (cont)
  ;;                       #f
  ;;                       (StateT           ; s₀ (κ)
  ;;                        #f
  ;;                        (NondetT ID))))))))

  (define-monad (ReaderT                      ; r₂ (env)
                 (ReaderT                     ; r₁ (ξ)
                  (StateT                     ; s₃ (store)
                   #f (StateT                 ; s₂ (σ)
                       #f (NondetT
                           (StateT            ; s₁ (cont)
                            (FinMapO PowerO)
                            (StateT           ; s₀ (κ)
                             (FinMapO PowerO)
                             ID))))))))

  (define ask-env (bind ask (compose1 return car)))
  (define ask-ξ   (bind ask (compose1 return cdr)))
  (define (local-env env xM)
    (do (cons _ ξ) ← ask
        (local (cons env ξ) xM)))
  (define (local-ξ ξ xM)
    (do (cons env _) ← ask
        (local (cons env ξ) xM)))

  (define get-store (bind get (compose1 return car)))
  (define get-σ     (bind get (compose1 return cadr)))
  (define get-cont  (bind get (compose1 return caddr)))
  (define get-κ     (bind get (compose1 return cdddr)))
  (define (put-store s)
    (do `(,_ ,σ ,c . ,κ) ← get
        (put `(,s ,σ ,c . ,κ))))
  (define (put-σ σ)
    (do `(,s ,_ ,c . ,κ) ← get
        (put `(,s ,σ ,c . ,κ))))
  (define (put-cont c)
    (do `(,s ,σ ,_ . ,κ) ← get
        (put `(,s ,σ ,c . ,κ))))
  (define (put-κ κ)
    (do `(,s ,σ ,c . ,_) ← get
        (put `(,s ,σ ,c . ,κ))))

  (define (mrun m)
    (run-StateT
     (map-∅ 'κ (set 0)) ; (FinMapO PowerO)
     (run-StateT
      (map-∅ 'cont (set 1)) ; (FinMapO PowerO)
      (run-StateT
       'σ
       (run-StateT
        'store
        (run-ReaderT
         'ξ
         (run-ReaderT
          'env
          m)))))))

  (check-equal? (mrun (local-ξ
                       'ξ′
                       (local-env
                        'env′
                        (do env ← ask-env
                            ξ ← ask-ξ
                            s ← get-store
                            (put-store 'foo)
                            κ ← get-κ
                            (put-κ (κ 'bar (set 'a 'b 'c)))
                            (return (list env ξ))))))
                (cons
                 (cons
                  (set (cons
                        (cons
                         (list 'env′ 'ξ′)
                         'foo)
                        'σ))
                  (map-∅ 'cont (set 1)))
                 ((map-∅ 'κ (set 0)) 'bar (set 'a 'b 'c)))))

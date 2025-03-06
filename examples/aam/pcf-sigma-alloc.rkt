#lang racket/base
(require lightstep/base lightstep/syntax
         (only-in "common.rkt" mmap-ext mmap-lookup)
         (only-in "pcf.rkt" δ)
         (only-in "pcf-rho.rkt" vρ)
         (only-in "pcf-varsigma.rkt" -->vς)
         (only-in "pcf-sigma.rkt"
                  [PCFσ orig-PCFσ] -->vσ injσ formals  alloc))
(provide -->vσ/alloc)

(module+ test
  (require rackunit)
  (require (only-in (submod "pcf.rkt" test) fact-5)))

;; Abstracting Abstract Machines from:
;;   https://dvanhorn.github.io/redex-aam-tutorial/

;; TODO: monadic version

;;-----------------------------------------------------------------------------
;; 3.9 Abstracting over alloc


(define-language PCFσ #:super orig-PCFσ)

(define-reduction (-->vσ/alloc alloc) #:super [(-->vσ)])

(define -->vσ (call-with-values (λ () (-->vσ/alloc alloc)) compose1))

(module+ test
  (check-equal?  (car ((repeated -->vσ) (injσ fact-5))) (set 120)))

(define (alloc-gensym σ)
  (match σ
    [`((((,M ,(? ρ?)) ,V ...) ,K) ,Σ)
     (map gensym (formals M))]))  

(module+ test
  (define --> (call-with-values (λ () (-->vσ/alloc alloc-gensym)) compose1))
  ;(car ((repeated step-->) (injσ '((λ ([x : num]) (λ ([y : num]) x)) 100))))
  (check-equal? (car ((repeated -->) (injσ fact-5))) (set 120)))

(define (alloc-nat σ)
  (match σ
    [`((((,M ,(? ρ?)) ,V ...) ,K) ,Σ)
     (let ([n (add1 (apply max 0 (set→list (dom Σ))))])
       (build-list (length (formals M))
                   (λ (i) (+ i n))))]))  

(module+ test
  (define -->′ (call-with-values (λ () (-->vσ/alloc alloc-nat)) compose1))
  ;(car ((repeated step-->′) (injσ '((λ ([x : num]) (λ ([y : num]) x)) 100))))
  (check-equal? (car ((repeated -->′) (injσ fact-5))) (set 120)))

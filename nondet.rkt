#lang racket/base
(require
 (for-syntax racket/base syntax/parse
             (only-in racket/syntax format-id)
             (only-in syntax/stx stx-map))
 (only-in "set.rkt" set ∅ ∅?)
 (only-in "match.rkt" match)
 (only-in "transformers.rkt" ID StateT NondetT with-monad run-StateT))
(provide NondetM nondet-match)

;;=============================================================================
;; nondet-match

(define NondetM (NondetT ID))

(struct nondet-pat (pats) #:transparent)

;; (match '()
;;   [(nondet-pat x (cons x y) `(,x ,y ...))
;;    'OK]
;;   [_ 'NG])

(match '()
  [(nondet-pat (list x (cons x y) `(,x ,y ...)))
   'OK]
  [_ 'NG])

(begin-for-syntax
  ;; If pat is expander, then do syntax-local-apply-transformer and
  ;; recurses expand-nondet with the result.
  ;; If nondet-pat, unfolds to multiple clauses.
  ;; Otherwise, it returns the result as is.
  (define (expand-nondet clause)
    (list clause))
  )

(define-syntax (nondet-match stx)
  (syntax-parse stx
    [(_ M:id x (~optional (~seq #:default dclause)) [pat body ...] ...)
     ;; M must be an identifier to transplant its lexical context. why?
     #:with do      (format-id #'M "do")
     #:with return  (format-id #'M "return")
     #:with mzero   (format-id #'M "mzero")
     #:with mconcat (format-id #'M "mconcat")

     #:with (((pat′ body′ ... e′) ...) ...) (stx-map expand-nondet
                                                     #'([pat body ...] ...))
     #:with nexts #'(with-monad M
                      (mconcat (match x
                                 [pat′ (do body′ ... (return e′))] ...
                                 [_ mzero])
                               ...))
     (if (and (attribute dclause) (syntax-e #'dclause))
       (with-syntax ([[pat body ...] #'dclause])
         (define/syntax-parse ((pat′ body′ ... e′) ...)
           (expand-nondet #'[pat body ...]))
         #'(let ([ςs nexts])
             (if (∅? ςs)
               (with-monad M
                 (match x
                   [pat′ (do body′ ... (return e′))] ...
                   [_ mzero]))
               ςs)))
       #'nexts)]))


(module+ test ;;test-nondet-match
  (require rackunit)

  (check-equal? (nondet-match NondetM '(1 2 3)
                              [x x]
                              [(list a b c) (+ a b c)])
                (set 6 '(1 2 3)))
  
  (check-equal? (nondet-match NondetM  (set 1 2 3)
                              [x x]
                              [(set a b c) (set (set a b) c)]
                              [(set a ...) (apply + a)])
                (set (set 1 (set 2 3)) (set 1 3 2) 6))

  (check-equal? (nondet-match NondetM (set 1 2 3)
                              [x (nondet-match NondetM x
                                               [(set a b c)
                                                (set (set a b) c)])]
                              [x (nondet-match NondetM x
                                               [(set a ...) (apply + a)])])
                (set (set 6) (set (set 1 (set 2 3)))))
  (check-equal? (nondet-match NondetM '(1 2 3)
                              [`(,x ...) x])
                (set '(1 2 3)))

  (check-equal? (nondet-match NondetM '(1 2 3)
                              #:default #f
                              [(list a b) (+ a b)])
                ∅)
  (check-equal? (nondet-match NondetM '(1 2 3)
                              #:default [xs xs]
                              [(list a b) (+ a b)])
                (set '(1 2 3)))
  (check-equal? (nondet-match NondetM '(1 2 3)
                              #:default [xs xs]
                              [(list a b c) (+ a b c)])
                (set 6))

  (define SRM (StateT #f NondetM))
  (check-equal? (run-StateT ∅ (nondet-match SRM '(1 2 3)
                                            [x
                                             `(,_ ,y ...) ← (return x)
                                             y]
                                            [(list a b c) (+ a b c)]))
                (set (cons 6 ∅) (cons '(2 3) ∅))))

;; TODO: define-nondet-match-expander
;;   with syntax-local-apply-transformer
(begin-for-syntax
 (struct nondet-match-expander (proc)))

(define-syntax (define-nondet-match-expander stx)
  (syntax-parse stx
    [(_ id:id proc)
     (syntax/loc #'stx
       (define-syntax id (nondet-match-expander proc)))]))

(define-nondet-match-expander hoge
  (λ (stx)
    (syntax-parse stx
      [(x ...) #'(x ... x ...)])))

(define-syntax (apply-expander stx)
  (syntax-parse stx
    ([_ id expr]
     (let ([expander (syntax-local-value #'id)])
       (if (nondet-match-expander? expander)
         (let ([expander (nondet-match-expander-proc expander)])
           (with-syntax ([expr′
                          ;(expander #'expr)
                          (syntax-local-apply-transformer
                           expander #f #;#'id 'expression #f
                           #'expr)])
             #''expr′))
         (raise-syntax-error #f "not a nondet-expander" stx #'id))))))

(apply-expander hoge (+ 1 2))

#lang racket/base
(require
 (for-syntax racket/base racket/syntax syntax/parse
             (only-in racket/syntax format-id)
             (only-in syntax/stx stx-map))
 (only-in "set.rkt" set ∅ ∅?)
 (only-in "match.rkt" match)
 (only-in "transformers.rkt" ID StateT NondetT with-monad run-StateT))
(provide NondetM nondet nondet-match define-nondet-match-expander)

(module+ test (require rackunit))

;;=============================================================================
;; define-nondet-match-expander

(define-syntax (define-nondet-match-expander stx)
  (syntax-parse stx
    [(_ id:id proc)
     (syntax/loc #'stx
       (define-syntax id (nondet-match-expander proc)))]))

(module+ test
  (define-nondet-match-expander mycons
    (λ (stx)
      (syntax-parse stx
        [(_ a b) #'(cons a b)])))

  (define-nondet-match-expander mytriple
    (λ (stx)
      (syntax-parse stx
        [(_ x y z) #'(mycons x (mycons y (mycons z '())))])))

  (check-equal? (nondet-match NondetM '(1 2 3)
                              [x x]
                              [(mycons a b) (apply + a b)])
                (set 6 '(1 2 3)))

  (check-equal? (nondet-match NondetM '(1 2 3)
                              [x x]
                              [(mytriple a b c) (+ a b c)])
                (set 6 '(1 2 3))))


;;=============================================================================
;; nondet-match

(define NondetM (NondetT ID))

;; (nondet p ...) pattern
(define-syntax nondet (λ (stx) (raise-syntax-error
                                #f "must not be used outside pattern" stx)))

(begin-for-syntax
  (struct nondet-match-expander (proc))

  (define (parse pat)
    (syntax-parse pat
      [(id:id . args)
        #:do [(define lval (syntax-local-value/record
                            #'id nondet-match-expander?))]
        #:when lval
        (let ([expander (nondet-match-expander-proc lval)])
          (with-syntax ([pat′ (syntax-local-apply-transformer
                               expander #'id 'expression #f
                               #'(id . args))])
            (parse #'pat′)))]
      [(p ...)
       #:with (p′ ...) (stx-map parse #'(p ...))
       #'(p′ ...)]
      [p #'p]))

  (define (expand-nondet pat)
    (syntax-parse pat
      #:literals (nondet)

      [(nondet p ...)
       #:with ((p′ ...) ...) (stx-map expand-nondet #'(p ...))
       #'(p′ ... ...)]
      
      [p #'(p)]))

  (define (expand-clause clause)
    (syntax-parse clause
      [(pat body ...)
       #:with pat′ (parse #'pat)
       #:with (pat″ ...) (expand-nondet #'pat′)
       #'([pat″ body ...] ...)])))

(define-syntax (nondet-match stx)
  (syntax-parse stx
    [(_ M:id x
        (~optional (~seq #:do [do-body ...]))
        [pat body ...] ...)
     ;; M must be an identifier to transplant its lexical context. why?
     #:with do      (format-id #'M "do")
     #:with return  (format-id #'M "return")
     #:with mzero   (format-id #'M "mzero")
     #:with mconcat (format-id #'M "mconcat")

     #:with (do-body′ ...) (if (attribute do-body)
                             #'(do-body ...)
                             #'())
     #:with (((pat′ body′ ... e′) ...) ...) (stx-map expand-clause
                                                     #'([pat body ...] ...))
     #'(with-monad M
         (let ()
           do-body′ ...
           (mconcat (match x
                      [pat′ (do body′ ... (return e′))]
                      [_ mzero]) ...
                    ...)))]))

(module+ test
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

  (define SRM (StateT #f NondetM))
  (check-equal? (run-StateT ∅ (nondet-match SRM '(1 2 3)
                                            [x
                                             `(,_ ,y ...) ← (return x)
                                             y]
                                            [(list a b c) (+ a b c)]))
                (set (cons 6 ∅) (cons '(2 3) ∅)))

  (check-equal? (nondet-match NondetM '(a 2) [`(,x ,y) x]) (set 'a))
  (check-equal? (nondet-match NondetM '(a 2) [`(,z ,x) x]) (set 2))
  (check-equal? (nondet-match NondetM '(a 2)
                              [`(,x ,y) x]
                              [`(,z ,x) x])
                (set 'a 2))

  (check-equal? (nondet-match NondetM '(a 2)
                              [(nondet `(,x ,y) `(,z ,x)) x])
                (set 'a 2))

  (check-equal? (nondet-match NondetM (set 1 2 3)
                              [(nondet (nondet x (set 1 x 2)) (set x 2 3)) x])
                (set (set 1 2 3) 3 1)))

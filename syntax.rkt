#lang racket/base
(require (for-syntax racket/base syntax/parse
                     (only-in racket/syntax define/with-syntax format-id)
                     (only-in "map.rkt" ↦ for/map ⊔ [∈ map-∈]))
         (only-in racket/list check-duplicates)
         (only-in "set.rkt" ∈ ∪)
         (only-in "match.rkt" match))
(provide define-language unique symbol-not-in)

(module+ test (require rackunit))

;;=============================================================================
;; define-language

(define-syntax (define-nonterminal stx)
  (syntax-parse stx
    [(_ N pat ...)
     #:with N? (format-id #'N "~a?" (syntax-e #'N) #:source #'N)
     (syntax/loc #'N
       (define (N? x)
         (match x [pat #t] ... [_ #f])))]))

;; TODO: auto generate Gen of rackcheck from the definition
(define-syntax (define-language stx)
  (syntax-parse stx
    #:datum-literals (∷= ::=)
    [(_ L:id (~optional (~seq #:super S:id)) [N:id (~or ∷= ::=) pat ...] ...)
     (define sup-rules (if (and (attribute S) (syntax-e #'S))
                         (syntax-local-value #'S)
                         (↦)))
     (define this-rules (for/map ([r (syntax->datum #'([N (pat ...)] ...))])
                          (values (car r) (cadr r))))
     (define rules (⊔ sup-rules this-rules
                      #:combine (λ (old-pats new-pats)
                                  (if (eq? (car new-pats) '....)
                                    (append old-pats (cdr new-pats))
                                    new-pats))))
     (define/with-syntax ([N′ (pat′ ...)] ...)
       (for/list ([(n ps) (map-∈ rules)])
         (list (datum->syntax #'L n) (datum->syntax #'L ps))))
     #`(begin
         #,(syntax/loc #'stx (define-syntax L (↦ ['N′ '(pat′ ...)] ...)))
         (define-nonterminal N′ pat′ ...) ...)
     ]))

;;=============================================================================
;; others

(define unique (compose1 not check-duplicates))

(module+ test
  (check-true  (unique '()))
  (check-true  (unique '(1)))
  (check-true  (unique '(1 2)))
  (check-false (unique '(1 2 3 2))))

(define ((symbol-not-in . ss) s)
  (if (∈ s (apply ∪ ss))
    (gensym s)
    s))

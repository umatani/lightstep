#lang racket/base
(require (for-syntax racket/base racket/syntax syntax/parse
                     (only-in racket/list splitf-at)
                     (only-in syntax/stx stx-map))
         (only-in racket/match [match r:match]))
(provide match match* match-λ match-λ* match-let
         (rename-out [match-λ match-lambda] [match-λ* match-lambda*])
         (for-syntax category-id? category-id→pred-id
                     (rename-out [category-id→pred-id
                                  category-id->pred-id])))

;; ID... is a synonym for (? ID? ID...)
;; (Camel cases are reserved for struct names)
(begin-for-syntax
  (define (category-id? id)
    (and (identifier? id)
         (let*-values ([(cs) (string->list
                              (symbol->string (syntax->datum id)))]
                       [(front back) (splitf-at cs char-upper-case?)])
           (and (not (null? front))
                (andmap (compose1 not char-lower-case?) back)))))

  (define (category-id→pred-id id)
    (and (identifier? id)
         (let*-values ([(cs) (string->list
                              (symbol->string (syntax->datum id)))]
                       [(front back) (splitf-at cs char-upper-case?)])
           (if (and (not (null? front))
                    (andmap (compose1 not char-lower-case?) back))
             (format-id id "~a?" (list->string front))
             #f))))

  (define (convert-category-id pat)
    (syntax-parse pat
      [x:id
       (if (category-id? #'x)
         #`(? #,(category-id→pred-id #'x) x)
         #'x)]
      [((~datum ?) e p ...)
       #'(? e p ...)]
      [(p ...)
       #:with (p′ ...) (stx-map convert-category-id #'(p ...))
       #'(p′ ...)]
      [p #'p]))
  )

(define-syntax (match stx)
  (syntax-parse stx
    [(_ expr [pat . rest] ...)
     #:with (pat′ ...) (stx-map convert-category-id #'(pat ...))
     #'(r:match expr [pat′ . rest] ...)]))

(define-syntax (match* stx)
  (syntax-parse stx
    [(_ (expr ...+) [(pat ...+) . rest] ...)
     #'(match (list expr ...)
         [(list pat ...) . rest] ...)]))

(define-syntax-rule (match-λ clause ...) (λ (id) (match id clause ...)))

(define-syntax-rule (match-λ* clause ...) (λ lst (match lst clause ...)))

;; match-let
(define-syntax (match-let stx)
  (syntax-parse stx
    [(_ ([pat expr] ...) body ...+)
     #'((match-λ* [(list pat ...) body ...])
        expr ...)]))

(module+ test
  (define NUM? number?)
  (define X? symbol?)

  (match '(1 2 3)
    [(cons NUM (cons NUM₁ x)) (list NUM x NUM₁)])

  (match* ('(1 2)
           #(1 2 3 4))
    [((list a b) (vector x ...))
     (list b a x)])

  ((match-λ [s s]) 3)
  ;((match-λ [X′ X′]) 3)
  ((match-λ [X′ X′]) 'foo)

  ((match-λ* [(list (list a b) (vector x ...))
              (list b a x)])
   '(1 2)
   #(1 2 3 4))
  
  (match-let ([(list a b) '(1 2)]
              [(vector x ...) #(a b c d)])
    (list b a x))
  ;; (match-let ([(list a b) '(1 2)]
  ;;             [(vector NUM′ ...) #(a b c d)])
  ;;   (list b a NUM′))
  (match-let ([(list a b) '(1 2)]
              [(vector NUM′ ...) #(1 2 3 4)])
    (list b a NUM′))
  ;; (match-let ([(list a b) '(1 2)]
  ;;             [(vector X ...) #(1 2 3 4)])
  ;;   (list b a X))
  (match-let ([(list a b) '(1 2)]
              [(vector X₁ ...) #(a b c d)])
    (list b a X₁))
  )

#lang racket/base
(require (for-syntax racket/base syntax/parse
                     (only-in racket/syntax format-id)
                     (only-in racket/list splitf-at)
                     (only-in syntax/stx stx-map))
         (only-in racket/match [match r:match]))
(provide match match* match-λ match-λ* match-let
         define/match
         (rename-out [match-λ match-lambda] [match-λ* match-lambda*])
         (for-syntax category-id? category-id→pred-id
                     (rename-out [category-id→pred-id
                                  category-id->pred-id])))

(module+ test (require rackunit))

;; TODO: why cannot write (? (λ (x) (equal? 'foo x))) in pattern

;; ID... is a synonym for (? ID? ID...)
;; (Camel cases are reserved for struct names)
(begin-for-syntax
  (define (category-id? id)
    (and (identifier? id)
         (let*-values ([(cs) (string->list
                              (symbol->string (syntax->datum id)))]
                       [(front back) (splitf-at cs char-upper-case?)])
           (and (not (null? front))
                (andmap (compose1 not
                                  (λ (c)
                                    (or (char=? c #\?)
                                        (char-lower-case? c))))
                        back)))))

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
      [p #'p])))

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

(define-syntax (define/match stx)
  (define-syntax-class header
    #:attributes [f (param 1) single?]
    (pattern (f:id x:id)
             #:attr (param 1) (syntax->list #'(x))
             #:attr single? #t)
    (pattern (f:id y:id ...)
             #:attr (param 1) (syntax->list #'(y ...))
             #:attr single? #f))
  (define-splicing-syntax-class option
    (pattern (~optional (~seq #:super g))
             #:with super #'(~? g #f)))

  (define (make-pat single? pat)
    (if single?
      #`(#,pat)
      pat))

  (syntax-parse stx
    [(_ h:header o:option
        [ps body ...] ...)
     #:with f #'h.f
     #:with g #'o.super
     #:with (x ...) #'(h.param ...)
     #:with ((pat ...) ...) (stx-map
                             (λ (p) (make-pat (attribute h.single?) p))
                             #'(ps ...))
     #:with (sup-clause ...) (if (syntax-e #'g)
                               (datum->syntax
                                #'f
                                ((syntax-local-value #'g)))
                               #'())
     #:with (clause ...) #'([`(,pat ...) body ...]
                            ...
                            sup-clause ...)
     #'(begin
         (define f-body
           (procedure-rename (λ (x ...) (match `(,x ...) clause ...))
                             'f))
         (define-syntax f
           (case-λ
            [() '(clause ...)]
            [(stx) (syntax-parse stx
                     [_:id #'f-body]
                     [(_ arg (... ...)) #'(f-body arg (... ...))])])))]))

(module+ test
  (define NUM? number?)
  (define X? symbol?)

  (check-equal? (match '(1 2 3)
                  [(cons NUM (cons NUM₁ x)) (list NUM x NUM₁)])
                '(1 (3) 2))

  (check-equal? (match '(1 2 3)
                  [`(,(? number? A) ,□ ,(? number?))
                   `(,A ,□ ,A)])
                '(1 2 1))

  (check-equal? (match '(1 2 3)
                  [`(,(? number? A) ,□ ,NUM″)
                   `(,NUM″ ,□ ,A)])
                '(3 2 1))

  (check-equal? (match '(1 2 3)
                  [`(,(? number? A) ,□ ,(? NUM? NUM″))
                   `(,NUM″ ,□ ,A)])
                '(3 2 1))

  (check-equal? (match* ('(1 2)
                         #(1 2 3 4))
                  [((list a b) (vector x ...))
                   (list b a x)])
                '(2 1 (1 2 3 4)))

  (check-equal? ((match-λ [s s]) 3) 3)
  ;((match-λ [X′ X′]) 3)
  (check-equal? ((match-λ [X′ X′]) 'foo) 'foo)
  
  (check-equal? ((match-λ* [(list (list a b) (vector x ...))
                            (list b a x)])
                 '(1 2)
                 #(1 2 3 4))
                '(2 1 (1 2 3 4)))
  
  (check-equal? (match-let ([(list a b) '(1 2)]
                            [(vector x ...) #(a b c d)])
                  (list b a x))
                '(2 1 (a b c d)))
  ;; (match-let ([(list a b) '(1 2)]
  ;;             [(vector NUM′ ...) #(a b c d)])
  ;;   (list b a NUM′))
  (check-equal? (match-let ([(list a b) '(1 2)]
                            [(vector NUM′ ...) #(1 2 3 4)])
                  (list b a NUM′))
                '(2 1 (1 2 3 4)))
  ;; (match-let ([(list a b) '(1 2)]
  ;;             [(vector X ...) #(1 2 3 4)])
  ;;   (list b a X))
  (check-equal? (match-let ([(list a b) '(1 2)]
                            [(vector X₁ ...) #(a b c d)])
                  (list b a X₁))
                '(2 1 (a b c d)))


  (define/match (f x)
    [1 'one]
    [2 'two]
    [_ 'other])
  (check-equal? (f 1) 'one)
  (check-equal? (f 2) 'two)
  (check-equal? (f 3) 'other)

  (define/match (g x y z)
    [(1 y _) (list 'one y)]
    [(2 _ z) (list 'two z)]
    [(_ y z) (list 'other y z)])
  (check-equal? (g 1 'a 'b) '(one a))
  (check-equal? (g 2 'c 'd) '(two d))
  (check-equal? (g 3 'e 'f) '(other e f))

  (define/match (ff x) #:super f
    [0 'zero])
  (check-equal? (ff 0) 'zero)
  (check-equal? (ff 1) 'one)
  (check-equal? (ff 2) 'two)
  (check-equal? (ff 3) 'other)

  (define/match (gg x y z) #:super g
    [(0 _ _) (list 'zero)])
  (check-equal? (gg 0 'a 'b) '(zero))
  (check-equal? (gg 1 'a 'b) '(one a))
  (check-equal? (gg 2 'c 'd) '(two d))
  (check-equal? (gg 3 'e 'f) '(other e f)))

#lang racket/base
(require (for-syntax racket/base syntax/parse
                     (only-in racket/syntax define/with-syntax format-id)
                     (only-in syntax/stx stx-map)
                     (only-in "map.rkt" ↦ for/map ⊔ [∈ map-∈] in-map))
         (only-in racket/list check-duplicates)
         (only-in "set.rkt" ∈ ∪)
         (only-in racket/match define-match-expander)
         (only-in "match.rkt" match match-λ category-id?)
         (only-in "nondet.rkt" define-nondet-match-expander nondet))
(provide define-language cxt nondet-cxt unique symbol-not-in)

(module+ test (require rackunit))

;;=============================================================================
;; define-language

(define-syntax (define-nonterminal stx)
  (syntax-parse stx
    [(_ N pat ...)
     #:with N? (format-id #'N "~a?" (syntax-e #'N) #:source #'N)
     ;; #'(define (N? x)
     ;;     (match x [pat #t] ... [_ #f]))
     (syntax/loc stx
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
     (for ([(n ps) (in-map rules)])
       (when (eq? (car ps) '....)
         (raise-syntax-error #f (format "unknown super category ~s" n) stx)))
     (define/with-syntax ([N′ (pat′ ...)] ...)
       (for/list ([(n ps) (map-∈ rules)])
         (list (datum->syntax #'L n) (datum->syntax #'L ps))))
     #`(begin
         (define-syntax L (↦ ['N′ '(pat′ ...)] ...))
         ;#,(syntax/loc stx (define-syntax L (↦ ['N′ '(pat′ ...)] ...)))
         ;(define-nonterminal N′ pat′ ...) ...
         #,@(stx-map (λ (c) (quasisyntax/loc stx
                              (define-nonterminal #,@c)))
                     #'((N′ pat′ ...) ...)))]))

;;=============================================================================
;; cxt

(begin-for-syntax
  (define (with-ctor/list stx)
    (syntax-parse stx
      [() #'(() '())]

      [(p₀ (~datum ...) p₁ ...)
       #:with (p₀′ c₀) (with-ctor #'p₀)
       #:with (p₀″ n₀) (if (identifier? #'c₀)
                         #'(p₀′ c₀)
                         (with-syntax ([(n) (generate-temporaries #'(n))])
                           #'((and n p₀′) n)))
       #:with ((p₁′ ...) c₁) (with-ctor/list #'(p₁ ...))
       #'((p₀″ (... ...) p₁′ ...) (append n₀ c₁))]

      [(p₀ p₁ ...)
       #:with (p₀′ c₀) (with-ctor #'p₀)
       #:with ((p₁′ ...) c₁) (with-ctor/list #'(p₁ ...))
       #'((p₀′ p₁′ ...) (cons c₀ c₁))]

      [p (raise-syntax-error 'with-ctor/list "unknown pattern" #'p)]))

  (define (with-ctor/quasi qp)
    (syntax-parse qp
      #:literals (unquote unquote-splicing)

      [() #'(() '())]

      [x:id #'(x 'x)]

      [(unquote p)
       #:with (p′ c) (with-ctor #'p)
       #'((unquote p′) c)]

      [((unquote-splicing p₀) qp₁ ...)
       #:with (p₀′ c₀) (with-ctor #'p₀)
       #:with (p₀″ n₀) (if (identifier? #'c₀)
                         #'(p₀′ c₀)
                         (with-syntax ([(n) (generate-temporaries #'(n))])
                           #'((unquote (and n (quasiquote p₀′))) n)))
       #:with ((qp₁′ ...) c₁) (with-ctor/quasi #'(qp₁ ...))
       #'(((unquote-splicing p₀″) qp₁′ ...) (append n₀ c₁))]

      [(qp₀ (~datum ...) qp₁ ...)
       #:with (qp₀′ c₀) (with-ctor/quasi #'qp₀)
       #:with (qp₀″ n₀) (if (identifier? #'c₀)
                          #'(qp₀′ c₀)
                          (with-syntax ([(n) (generate-temporaries #'(n))])
                            #'((unquote (and n (quasiquote qp₀′))) n)))
       #:with ((qp₁′ ...) c₁) (with-ctor/quasi #'(qp₁ ...))
       #'((qp₀″ (... ...) qp₁′ ...) (append n₀ c₁))]

      [(qp₀ qp₁ ...)
       #:with (qp₀′ c₀) (with-ctor/quasi #'qp₀)
       #:with ((qp₁′ ...) c₁) (with-ctor/quasi #'(qp₁ ...))
       #'((qp₀′ qp₁′ ...) (cons c₀ c₁))]

      [b:boolean #'(b b)]
      [c:char    #'(c c)]
      [k:keyword #'(k k)]
      [n:number  #'(n n)]
      [s:str     #'(s s)]

      [p (raise-syntax-error 'with-ctor/quasi "unknown pattern" #'p)]))
  
  (define (with-ctor pat)
    (syntax-parse pat
      #:literals (quote quasiquote list cons)

      [(quote x)
       #'((quote x) (quote x))]

      [(quasiquote qp)
       #:with (qp′ c) (with-ctor/quasi #'qp)
       #'((quasiquote qp′) c)]

      [(list p ...)
       #:with ((p′ ...) c) (with-ctor/list #'(p ...))
       #'((list p′ ...) c)]

      [(cons p₀ p₁)
       #:with (p₀′ c₀) (with-ctor #'p₀)
       #:with (p₁′ c₁) (with-ctor #'p₁)
       #'((cons p₀′ p₁′) (cons c₀ c₁))]

      [((~datum ?) e x:id)  ;; tiny hack
       #'((? e x) x)]

      [((~datum ?) e p ...) ;; general case
       #:with (n) (generate-temporaries #'(n))
       #'((? e n p ...) n)]

      [x:id
       (if (category-id? #'x)
         (with-syntax ([(n) (generate-temporaries #'(n))])
           #'((and n x) n))
         #'(x x))]

      [b:boolean #'(b b)]
      [c:char    #'(c c)]
      [k:keyword #'(k k)]
      [n:number  #'(n n)]
      [s:str     #'(s s)]

      [p (raise-syntax-error 'with-ctor "unknown pattern" #'p)]))

  (define (nondet-cxt1 stx)
    (syntax-parse stx
      [(C:id hole:id p)
       #:with (p′ c) (with-ctor #'p)
       #'(and p (app (match-λ [p′ (λ (hole) c)]) C))])))

(define-nondet-match-expander nondet-cxt
  (syntax-parser
    [(_ C:id hole:id p ...)
     #:with (p′ ...) (stx-map (λ (p) (nondet-cxt1 #`(C hole #,p))) #'(p ...))
     #'(nondet p′ ...)]))


(define-match-expander cxt
  (syntax-parser
    [(_ C:id [□:id p₁] p ...)
     #:with ((p′ c) ...) (stx-map with-ctor #'(p ...))
     #'(app (letrec ([chk (λ (f e)
                            (match e
                              [p′
                               #:do [(define r (chk (λ (□) (f c)) □))]
                               #:when r
                               r]
                              ...
                              [p₁ (cons f e)]
                              [_ #f]))])
              (λ (e) (chk (λ (x) x) e)))
            (cons C p₁))]))

(module+ test
  (check-equal? (match '(1 (a (b c))) ; '((λ x x) (+ 1 2))
                  [(cxt Ce [□ (? symbol? □)]
                        `(,(? number?) ,□)
                        `(,(? symbol?) ,□)
                        `(,□ ,y)
                        )
                   (list (Ce (string->symbol (format "~a′" □))) □)]
                  [_ 'NG])
                '((1 (a (b c′))) c)))


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

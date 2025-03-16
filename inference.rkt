#lang racket/base
(require (for-syntax racket/base syntax/parse
                     (only-in racket/list append-map)
                     (only-in racket/match match match-define match-λ)
                     (only-in racket/syntax format-id syntax-local-eval)
                     (only-in syntax/stx stx-map)
                     racket/pretty)
         (only-in "reduction.rkt" define-reduction reducer-of escape-elipsis
                  [options roptions] gen-rname))
(provide define-inference)

(module+ test (require rackunit))

(begin-for-syntax
  ;; for debug
  (define (print-σ σ)
    (for ([kv (in-list σ)])
      (printf "~a ↦ ~a\n"
              (pretty-format (syntax->datum (car kv)))
              (pretty-format (syntax->datum (cdr kv))))))
  
  (define-syntax-class hbar
    (pattern x:id
             #:when (regexp-match #px"-{3,}"
                                  (symbol->string (syntax-e #'x)))))

  (define-splicing-syntax-class (options rid)
    (pattern (~seq (~alt (~optional
                          (~seq #:forms ((~or* (~datum ....) [p₀ #:where . r₀])
                                         [p #:where . r] ...))
                          #:name "#:forms option"
                          #:defaults ([p₀ #'`(,i:i → ,o:o)]
                                      [r₀ #`(o ← (#,rid i))]
                                      [(p 1) '()]
                                      [(r 1) '()])))
                   ...)
             #:with (pat ...) #'(p₀ p ...)
             #:with (rhs ...) #'(r₀ r ...)))

  (define (name&mode id)
    (define id-str (symbol->string (syntax-e id)))
    (match-define (list name mode)
      (cond
        [(regexp-match #px"^([^:]*):([^:]*)$" id-str) => cdr]
        [else (list id-str "n")]))
    (match mode
      ["i" (list '#:in   (format-id id name))]
      ["o" (list '#:out  (format-id id name))]
      ["n" (list '#:none (format-id id name))]
      [_ (raise-syntax-error #f "unknown mode" id)]))


  (define (match-form/list pats forms σ)
    (define pair #`(#,pats #,forms))
    ;(printf "match-form/list: ~a\n" (pretty-format (syntax->datum pair)))
    (define (err) `(ERR ,(format "no match: ~a" (syntax->datum pair))))

    (syntax-parse pair
      [(() ()) σ]

      ;; TODO?
      ;; [(p₀ (~datum ...) p₁ ...)
      ;;  #'(void)]

      [((p₀ p₁ ...) (f₀ f₁ ...))
       (match (match-form #'p₀ #'f₀ σ)
         [`(ERR ,msg) `(ERR ,msg)]
         [σ′ (match-form/list #'(p₁ ...) #'(f₁ ...) σ′)])]

      [_ (err)]))

  (define (match-form/quasi qp form σ)
    (define pair #`(#,qp #,form))
    ;(printf "match-form/quasi: ~a\n" (pretty-format (syntax->datum pair)))
    (define (err) `(ERR ,(format "no match: ~a" (syntax->datum pair))))

    (syntax-parse pair
      #:literals (unquote unquote-splicing)

      [(() ()) σ]

      [(x:id x′:id)
       (if (eq? (syntax-e #'x) (syntax-e #'x′)) σ (err))]

      [((unquote p) (unquote f))
       (match-form #'p #'f σ)]

      [((unquote p) f)
       (match-form #'p #'(quasiquote f) σ)]

      ;; TODO?
      ;; [((unquote-splicing p₀) qp₁ ...)
      ;;  #'(void)]

      ;; TODO?
      ;; [(qp₀ (~datum ...) qp₁ ...)
      ;;  #'(void)]

      [((qp₀ qp₁ ...) (f₀ f₁ ...))
       (match (match-form/quasi #'qp₀ #'f₀ σ)
         [`(ERR ,msg) `(ERR ,msg)]
         [σ′ (match-form/quasi #'(qp₁ ...) #'(f₁ ...) σ′)])]

      [(b:boolean b′)
       (if (equal? (syntax->datum #'b) (syntax->datum #'b′)) σ (err))]
      [(c:char c′)
       (if (equal? (syntax->datum #'c) (syntax->datum #'c′)) σ (err))]
      [(k:keyword k′)
       (if (equal? (syntax->datum #'k) (syntax->datum #'k′)) σ (err))]
      [(n:number n′)
       (if (equal? (syntax->datum #'n) (syntax->datum #'n′)) σ (err))]
      [(s:str s′)
       (if (equal? (syntax->datum #'s) (syntax->datum #'s′)) σ (err))]

      [_ (err)]))

  (define (match-form pat form σ)
    (define pair #`(#,pat #,form))
    ;(printf "match-form: ~a\n" (pretty-format (syntax->datum pair)))
    (define (err) `(ERR ,(format "no match: ~a" (syntax->datum pair))))

    (syntax-parse pair
      #:literals (quote quasiquote list cons)

      ;; =============================================================
      ;; TODO: more frexible combination of lists
      [((quote x) (quote x′))
       (if (equal? (syntax->datum #'x) (syntax->datum #'x′)) σ (err))]

      [((quasiquote qp) (quasiquote qf))
       (match-form/quasi #'qp #'qf σ)]
      [((quasiquote qp) (quote qf))
       (match-form/quasi #'qp #'qf σ)]

      [((list p ...) (list f ...))
       (match-form/list #'(p ...) #'(f ...) σ)]

      [((cons p₀ p₁) (cons f₀ f₁))
       (match (match-form #'p₀ #'f₀ σ)
         [`(ERR ,msg) `(ERR ,msg)]
         [σ′ (match-form #'p₁ #'f₁ σ′)])]
      ;; =============================================================

      ;; necessary?
      [(((~datum ?) e p ...) ((~datum ?) e′ f ...))
       (for/fold ([σ σ])
                 ([pp (syntax->list #'(p  ...))]
                  [ff (syntax->list #'(f ...))])
         (match σ
           [`(ERR ,msg) `(ERR ,msg)]
           [σ′ (match-form pp ff σ′)]))]

      [(x:id f)
       (match (name&mode #'x)
         [`(,mode ,name)
          (if (assoc name σ free-identifier=?)
            `(ERR ,(format "duplicate id in form pattern: ~a" (syntax-e name)))
            (cons (cons name `(,mode ,#'f)) σ))])]

      [(b:boolean b′)
       (if (equal? (syntax->datum #'b) (syntax->datum #'b′)) σ (err))]
      [(c:char c′)
       (if (equal? (syntax->datum #'c) (syntax->datum #'c′)) σ (err))]
      [(k:keyword k′)
       (if (equal? (syntax->datum #'k) (syntax->datum #'k′)) σ (err))]
      [(n:number n′)
       (if (equal? (syntax->datum #'n) (syntax->datum #'n′)) σ (err))]
      [(s:str s′)
       (if (equal? (syntax->datum #'s) (syntax->datum #'s′)) σ (err))]

      [_ (err)]))

  (define (xform-rule form-xformer main-pat premises concl rnam)
    (define σ
      (match (match-form main-pat concl '())
        [`(ERR ,msg) (raise-syntax-error 'xform-rule msg)]
        [σ σ]))
    (define-values (σᵢ σₒ) (for/fold ([σᵢ '()]
                                      [σₒ '()])
                                     ([x (in-list σ)])
                             (match-define (cons id mode&form) x)
                             (match mode&form
                               [`(#:in  ,f) (values (cons (cons id f) σᵢ) σₒ)]
                               [`(#:out ,f) (values σᵢ (cons (cons id f) σₒ))]
                               [`(,_ ,_) (values σᵢ σₒ)])))

    ;; (printf "[σᵢ]\n")
    ;; (print-σ σᵢ)
    ;; (printf "[σᵢ]\n")
    ;; (print-σ σₒ)

    (define in-pat
      (syntax-parse (map cdr σᵢ)
        [() (raise-syntax-error #f "no input specified in #:forms" main-pat)]
        [(form) #'form]
        [(form ...) #'(list form ...)]))

    (define out-expr
      (syntax-parse (map cdr σₒ)
        [() #'#t]
        [(form) #'form]
        [(form ...) #'(list form ...)]))

    (define premises′ (append-map form-xformer premises))

    #`(#,in-pat #,@premises′ #,out-expr #,rnam)))

(define-syntax (define-inference stx)
  (syntax-parse stx
    [(_ (rid:id param:id ...)
        ropts:roptions
        (~var opts (options #'rid))
        [frm ...
         _:hbar (~optional rnam:string
                           #:defaults ([rnam (gen-rname #'rid 'r)]))
         frm′]
        ...)
     #:with ([main-pat main-rhs]
             [form-pat rhs-expr] ...) #'([opts.pat opts.rhs] ...)

     #:do [(define (form-xformer form)
             (define (try-form pat rhs)
               (match (match-form pat form '())
                 [`(ERR ,_) #f]
                 [σ (with-syntax ([([p f] ...)
                                   (map (match-λ
                                         [(cons id f)
                                          (list id (escape-elipsis (cadr f)))])
                                        σ)])
                      (syntax-local-eval #`(with-syntax ([p #'f] ...)
                                             #'#,rhs)))]))
             (let loop ([pats (cons #'main-pat
                                    (syntax->list #'(form-pat ...)))]
                        [rhss (cons #'main-rhs
                                    (syntax->list #'(rhs-expr ...)))])
               (cond
                 [(null? pats) (list form)]
                 [(try-form (car pats) (car rhss))
                  => (λ (forms) (syntax->list forms))]
                 [else (loop (cdr pats) (cdr rhss))])))]
     #:with (rule′ ...) (stx-map (λ (ps c n)
                                   (xform-rule form-xformer #'main-pat
                                               (syntax->list ps) c n))
                                 #'((frm ...) ...)
                                 #'(frm′ ...)
                                 #'(rnam ...))

     #'(define-reduction (rid param ...)
         (~@ . ropts) rule′ ...)]))

(module+ test
  (require "set.rkt")

  (define-inference (r)
    #:forms ([`(,I:i → ,O:o) #:where O ← (r I)])

    [----------------------------- "car"
     `(,(cons a d) → ,a)])

  (define step-r (call-with-values (λ () (r)) compose1))
  (check-equal? (step-r (cons 1 2)) (set 1))

  (define-inference (r2)
    ;#:forms ([`(,I:i → ,O:o) #:where O ← (r2 I)])

    [`(,(cons a b) → ,(cons a′ d′))  ;; TODO `(,a → (,a′ . ,d′))
     ------------------------------ "caar"
     `(,(cons (cons a b) c) → ,a′)]

    [---------- "car"
     `(,(cons a b) → ,a)]

    [---------- "id"
     `(,a → ,a)])

  (define step-r2 (call-with-values (λ () (r2)) compose1))
  (check-equal? (step-r2 (cons (cons 1 2) 3))
                (set 1 (cons 1 2) (cons (cons 1 2) 3)))


  (define-inference (r3)
    ;#:forms ([`(,I:i → ,O:o) #:where O ← (r3 I)])

    [`(,(cons a b) → (,a′ . ,d′))
     ------------------------------ "caar"
     `(,(cons (cons a b) c) → ,a′)]

    [---------- "car"
     `(,(cons a b) → ,a)]

    [---------- "id"
     `(,a → ,a)])

  (define step-r3 (call-with-values (λ () (r3)) compose1))
  (check-equal? (step-r3 (cons (cons 1 2) 3))
                (set 1 (cons 1 2) (cons (cons 1 2) 3)))

  (define-inference (r4)
    ;#:forms ([`(,I:i → ,O:o) #:where O ← (r4 I)])

    [`(,(cons a b) → ,c)
     `(,c → ,d)
     ------------------------------ "caar"
     `(,(cons (cons a b) c) → ,d)]

    [---------- "car"
     `(,(cons a b) → ,a)]

    [---------- "id"
     `(,a → ,a)])

  (define step-r4 (call-with-values (λ () (r4)) compose1))
  (check-equal? (step-r4 (cons (cons 1 2) 3))
                (set 1 (cons 1 2) (cons (cons 1 2) 3))))

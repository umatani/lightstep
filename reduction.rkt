#lang racket/base
(require (for-syntax racket/base racket/syntax syntax/parse
                     (only-in racket/match match-define)
                     (only-in syntax/stx stx-map)
                     (only-in "set.rkt" list→set ∈))
         racket/require-syntax racket/provide-syntax
         (only-in racket/unit
                  define-signature unit import export link
                  compound-unit invoke-unit)
         (only-in racket/match match)
         (only-in "set.rkt" ∅ ∅? ∈ set set-add)
         (only-in "transformers.rkt"
                  ID ReaderT WriterT StateT FailT NondetT
                  run-ReaderT run-StateT
                  define-monad with-monad PowerO))
(provide ReduceM define-reduction repeated reduction-in reduction-out)


;;=============================================================================
;; nondet-match

(define ReduceM (NondetT ID))

(define-syntax (nondet-match stx)
  (syntax-parse stx
    [(_ M:id x #:default dclause [pat body ... e] ...)
     ;; M must be an identifier to transport lexical context. why?
     #:with do      (format-id #'M "do")
     #:with return  (format-id #'M "return")
     #:with mzero   (format-id #'M "mzero")
     #:with mconcat (format-id #'M "mconcat")
     #:with nexts #'(with-monad M
                      (mconcat (match x
                                 [pat (do body ... (return e))]
                                 [_ mzero])
                               ...))
     (if (syntax-e #'dclause)
       (with-syntax ([[pat body ... e] #'dclause])
         #'(let ([ςs nexts])
             (if (∅? ςs)
               (with-monad M
                 (match x
                   [pat (do body ... (return e))]
                   [_ mzero]))
               ςs)))
       #'nexts)]
    [(_ M x [pat body ... e] ...)
     #'(nondet-match M x #:default #f [pat body ... e] ...)]))


(module+ test ;;test-nondet-match
  (require rackunit)

  (check-equal? (nondet-match ReduceM '(1 2 3)
                              [x x]
                              [(list a b c) (+ a b c)])
                (set 6 '(1 2 3)))
  
  (check-equal? (nondet-match ReduceM  (set 1 2 3)
                              [x x]
                              [(set a b c) (set (set a b) c)]
                              [(set a ...) (apply + a)])
                (set (set 1 (set 2 3)) (set 1 3 2) 6))

  (check-equal? (nondet-match ReduceM (set 1 2 3)
                              [x (nondet-match ReduceM x
                                               [(set a b c)
                                                (set (set a b) c)])]
                              [x (nondet-match ReduceM x
                                               [(set a ...) (apply + a)])])
                (set (set 6) (set (set 1 (set 2 3)))))
  (check-equal? (nondet-match ReduceM '(1 2 3)
                              [`(,x ...) x])
                (set '(1 2 3)))

  (check-equal? (nondet-match ReduceM '(1 2 3)
                              [(list a b) (+ a b)])
                ∅)
  (check-equal? (nondet-match ReduceM '(1 2 3)
                              #:default [xs xs]
                              [(list a b) (+ a b)])
                (set '(1 2 3)))
  (check-equal? (nondet-match ReduceM '(1 2 3)
                              #:default [xs xs]
                              [(list a b c) (+ a b c)])
                (set 6))

  (define SRM (StateT #f ReduceM))
  (check-equal? (run-StateT ∅ (nondet-match SRM '(1 2 3)
                                            [x
                                             `(,_ ,y ...) ← (return x)
                                             y]
                                            [(list a b c) (+ a b c)]))
                (set (cons 6 ∅) (cons '(2 3) ∅))))

;;=============================================================================
;; define-reduction

(begin-for-syntax
  (define-splicing-syntax-class options
    (pattern (~seq (~alt (~optional (~seq #:monad m)
                                    #:name "#:monad option")
                         (~optional (~seq #:mrun mr)
                                    #:name "#:mrun option")
                         (~optional (~seq #:super (sname:id sarg ...))
                                    #:name "#:super option")
                         (~optional (~seq #:import [sig-spec ...])
                                    #:name "#:import option")
                         (~optional (~seq #:do [do-body ...])
                                    #:name "#:do option")
                         (~optional (~seq #:default [pat body ... e])
                                    #:name "#:default option")) ...)
             #:with monad     #'(~? m                #f)
             #:with mrun      #'(~? mr               #f)
             #:with sup-name  #'(~? sname            #f)
             #:with sup-args  #'(~? (sarg ...)       ())
             #:with imports   #'(~? (sig-spec ...)   ())
             #:with do-bodies #'(~? (do-body ...)    ())
             #:with default   #'(~? (pat body ... e) #f)))

  (define (replace-lexical-context lctx stx)
    (datum->syntax lctx (syntax->datum stx)))
  
  (define (escape-elipsis stx)
    (syntax-parse stx
      [x:id
       (if (eq? '... (syntax->datum #'x))
         (datum->syntax #'x '(... ...))
         #'x)]
      [(a ...)
       #:with (a′ ...) (stx-map escape-elipsis #'(a ...))
       #'(a′ ...)]
      [a #'a]))

  (struct reduction-desc (mrun import-sig expander))

  (define (inst-reduction-info rid args)
    (match-define
      (reduction-desc _ import-sig-stx expander-stx)
      (syntax-local-value rid))

    (define def-cxt (syntax-local-make-definition-context))
    (syntax-local-bind-syntaxes (list #'expander)
                                (escape-elipsis expander-stx) def-cxt)

    (syntax-parse (local-expand #`(expander #,@args ς)
                                'expression
                                (list #'nondet-match)
                                def-cxt)
      #:datum-literals [let-values nondet-match]
      [(let-values ()
         do-body ...
         (nondet-match _ _ #:default drule rule ...))
       #`(#,import-sig-stx
          (rule ...)
          (do-body ...)
          drule)]))

  (define (derive-mrun M)
    (syntax-parse M
      #:literals (ID ReaderT WriterT StateT FailT NondetT ReduceM)
      [ID      #'(λ (m) m)]
      [ReduceM #'(λ (m) m)]
      [(ReaderT M′)
       #:with (λ (p ...) b) (derive-mrun #'M′)
       #'(λ (r p ...) (run-ReaderT r ((λ (p ...) b) p ...)))]
      [(WriterT _ M′)
       (derive-mrun #'M′)]
      [(StateT _ M′)
       #:with (λ (p ...) b) (derive-mrun #'M′)
       #'(λ (s p ...) (run-StateT s ((λ (p ...) b) p ...)))]
      [(FailT M′)
       (derive-mrun #'M′)]
      [(NondetT M′)
       (derive-mrun #'M′)]
      [_ (raise-syntax-error 'derive-mrun "unknown monad" M)])))

(define-syntax (define-reduction stx)
  (define (gen-rnam stx sym)
    (datum->syntax stx (symbol->string (gensym sym))))

  (syntax-parse stx
    [(_ (rid:id param:id ...)
        opts:options
        [pat body ... (~and e (~not :string))
         (~optional rnam:string #:defaults ([rnam (gen-rnam #'rid 'r)]))]
        ...)
     #:do [(define (rescope stx)
             (replace-lexical-context #'rid stx))
           (define (rescope-and-escape-elipsis stx)
             (rescope (escape-elipsis stx)))
           (define overridden?
             (let ([rnams (list→set (syntax->datum #'(rnam ...)))])
               (syntax-parser
                 [(_ _ _ rnam _ ...)
                  (∈ (syntax-e #'rnam) rnams)])))]

     #:with M (if (syntax-e #'opts.monad)
                #'opts.monad
                #'ReduceM)
     #:with M′ (format-id #'rid "~a" (gensym 'M))

     #:with mrun (if (syntax-e #'opts.mrun)
                   #'opts.mrun
                   (derive-mrun #'M))

     #:with sup-rdesc (if (syntax-e #'opts.sup-name)
                        (format-id #'opts.sup-name "~a-info" #'opts.sup-name)
                        #'#f)
     #:with (imports-of-super
             rules-of-super
             do-bodies-of-super
             default-of-super)  (if (syntax-e #'sup-rdesc)
                                  (inst-reduction-info #'sup-rdesc
                                                       #'opts.sup-args)
                                  #'(() () () #f))

     #:with imports (stx-map rescope #`(#,@#'imports-of-super
                                        #,@#'opts.imports))

     #:with (sup-rule ...) (let ([rnams (list→set
                                         (syntax->datum #'(rnam ...)))])
                             (filter (compose1 not overridden?)
                                     (syntax->list #'rules-of-super)))

     #:with (rule ...) (stx-map rescope-and-escape-elipsis
                                #'(sup-rule ...
                                            [pat _ ≔ rnam body ... e] ...))

     #:with (do-body ...) (stx-map rescope-and-escape-elipsis
                                   #`(#,@#'do-bodies-of-super
                                      #,@#'opts.do-bodies))
     #:with default-clause (rescope-and-escape-elipsis
                            (if (syntax-e #'opts.default)
                              #'opts.default
                              #'default-of-super))

     #:with expander #'(λ (stx)
                         (syntax-parse stx
                           [(_ param ... ς)
                            #'(let ()
                                (define M′ M)
                                do-body ...
                                (nondet-match M′ ς
                                              #:default default-clause
                                              rule ...))]))
     
     #:with rdesc (format-id #'rid "~a-info" (syntax-e #'rid))
     #'(begin
         (define-syntax rdesc (reduction-desc #'mrun #'imports #'expander))
         (define-syntax (rid stx)
           (syntax-parse stx
             [(_ arg (... ...))
              #'(inst-reduction rdesc arg (... ...))])))]))

;;=============================================================================
;; inst-reduction

(define-syntax (inst-reduction stx)
  (syntax-parse stx
    [(_ rid:id arg ...)
     #:do [(match-define
             (reduction-desc mrun import-sigs expander-stx)
             (syntax-local-value #'rid))]

     #`(unit
         (import #,@import-sigs) (export)

         (define-signature M^
           ((define-syntaxes (inst) #,(escape-elipsis expander-stx))))

         (invoke-unit
          (compound-unit
           (import) (export)
           (link (([m : M^]) (unit (import) (export M^)))
                 (() (unit (import M^) (export)
                       (define (reducer ς) (inst arg ... ς))
                       (values #,mrun reducer))
                     m)))))]))

;;=============================================================================
;; reflexive and transitive closure

(define ((repeated →) ς)
  (define-monad (NondetT (StateT PowerO ID)))
  (define (search ς)
    (do Σ′ ≔ (→ ς)
        (if (∅? Σ′)
          (return ς)
          (do Σ ← get
              (for/monad+ ([ς′ Σ′]
                           #:unless (∈ ς′ Σ))
                (do (put (set-add Σ ς′))
                    (search ς′)))))))
  (run-StateT (set ς) (search ς)))


;;=============================================================================
;; custom require/provide spec

(define-require-syntax (reduction-in stx)
  (syntax-parse stx
    [(_ req-spec rid:id)
     #:with rdesc (format-id #'rid "~a-info" #'rid)
     #'(combine-in (only-in req-spec rid)
                   (only-in req-spec rdesc))]))

(define-provide-syntax (reduction-out stx)
  (syntax-parse stx
    [(_ rid:id)
     #:with rdesc (format-id #'rid "~a-info" #'rid)
     #'(combine-out rid rdesc)]))

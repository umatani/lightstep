#lang racket/base
(require (for-syntax racket/base syntax/parse
                     (only-in racket/syntax format-id)
                     (only-in racket/match match-define)
                     (only-in syntax/stx stx-map)
                     (only-in "set.rkt" list→set ∈))
         (only-in racket/require-syntax define-require-syntax)
         (only-in racket/provide-syntax define-provide-syntax)
         (only-in racket/unit
                 define-signature unit import export link
                 compound-unit invoke-unit)
         (only-in "set.rkt" set ∅? ⊆ set-add set-subtract)
         (only-in "transformers.rkt"
                  PowerO run-StateT define-monad
                  ID ReaderT WriterT StateT FailT NondetT)
         (only-in "nondet.rkt" NondetM nondet-match))
(provide ReduceM define-reduction repeated reduction-in reduction-out)

(define ReduceM NondetM)

;;=============================================================================
;; define-reduction

;; TODO: local-expandのかわりにsyntax-local-apply-transformer
;; TODO: inst-xformerをコンパイル時関数にしてescape不要に


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

  (struct reduction-desc (mrun import-sig inst-xformer))

  (define (inst-reduction-info rid args)
    (match-define
      (reduction-desc _ import-sig-stx inst-xformer-stx)
      (syntax-local-value rid))

    (define def-cxt (syntax-local-make-definition-context))
    (syntax-local-bind-syntaxes (list #'inst-xformer)
                                (escape-elipsis inst-xformer-stx) def-cxt)

    (syntax-parse (local-expand #`(inst-xformer #,@args ς)
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

     #:with inst-xformer #'(λ (stx)
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
         (define-syntax rdesc (reduction-desc #'mrun #'imports #'inst-xformer))
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
             (reduction-desc mrun import-sigs inst-xformer-stx)
             (syntax-local-value #'rid))]

     #`(unit
         (import #,@import-sigs) (export)

         (define-signature M^
           ((define-syntaxes (inst) #,(escape-elipsis inst-xformer-stx))))

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
    (do sΣ′ ≔ (→ ς)
        sΣ ← get
        (cond
          [(∅? sΣ′) (return ς)]
          [(⊆ sΣ′ sΣ) mzero]
          [(do (for/monad+ ([ς′ (set-subtract sΣ′ sΣ)])
                 (do (put (set-add sΣ ς′))
                     (search ς′))))])))
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

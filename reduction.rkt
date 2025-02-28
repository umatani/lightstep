#lang racket/base
(require (for-syntax racket/base syntax/parse
                     (only-in racket/syntax format-id)
                     (only-in racket/match match-define)
                     (only-in syntax/stx stx-map)
                     (only-in "set.rkt" list→set ∈))
         (only-in racket/unit
                 define-signature unit import export link
                 compound-unit invoke-unit)
         (only-in "set.rkt" set ∅? ⊆ set-add set-subtract)
         (only-in "transformers.rkt"
                  PowerO run-StateT define-monad
                  ID ReaderT WriterT StateT FailT NondetT)
         (only-in "nondet.rkt" NondetM nondet-match))
(provide ReduceM define-reduction repeated)

(define ReduceM NondetM)

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

  (struct reduction-desc (mrun import-sig inst-xformer))

  (define (inst-reduction-info rid args)
    (match-define
      (reduction-desc _ import-sig-stx inst-xformer)
      ((syntax-local-value rid) 'DUMMY))

    (syntax-parse
        ;; both can work
        ;; (inst-xformer #`(#,@args ς))
        (syntax-local-apply-transformer inst-xformer rid 'expression #f
                                        #`(#,@args ς))
      #:datum-literals [let nondet-match]
      [(let ()
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

;; TODO: multiple inheritance
;;   signal error at name conflict
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

     #:with (imports-of-super
             rules-of-super
             do-bodies-of-super
             default-of-super)  (if (syntax-e #'opts.sup-name)
                                  (inst-reduction-info #'opts.sup-name
                                                       #'opts.sup-args)
                                  #'(() () () #f))

     #:with imports (stx-map rescope #`(#,@#'imports-of-super
                                        #,@#'opts.imports))

     #:with (sup-rule ...) (let ([rnams (list→set
                                         (syntax->datum #'(rnam ...)))])
                             (filter (compose1 not overridden?)
                                     (syntax->list #'rules-of-super)))

     #:with (rule ...) (stx-map rescope
                                #'(sup-rule ...
                                            [pat _ ≔ rnam body ... e] ...))

     #:with (do-body ...) (stx-map rescope
                                   #`(#,@#'do-bodies-of-super
                                      #,@#'opts.do-bodies))
     
     #:with default-clause (rescope
                            (if (syntax-e #'opts.default)
                              #'opts.default
                              #'default-of-super))

     #:with inst-xformer (escape-elipsis
                          #'(λ (stx)
                              (syntax-parse stx
                                [(param ... ς)
                                 #'(let ()
                                     (define M′ M)
                                     do-body ...
                                     (nondet-match M′ ς
                                                   #:default default-clause
                                                   rule ...))])))
     #'(begin
         (define-syntax (rid stx)
           (define rdesc (reduction-desc #'mrun #'imports inst-xformer))
           (if (syntax? stx)
             (syntax-parse stx
               [(_ arg (... ...))
                #'(inst-reduction rid arg (... ...))])
             rdesc)))]))

;;=============================================================================
;; inst-reduction

(define-syntax (inst-reduction stx)
  (syntax-parse stx
    [(_ rid:id arg ...)
     #:do [(match-define
             (reduction-desc mrun import-sigs inst-xformer)
             ((syntax-local-value #'rid) 'DUMMY))]
     #`(unit
         (import #,@import-sigs) (export)
         (define (reducer ς) #,(inst-xformer #'(arg ... ς)))
         (values #,mrun reducer))]))

;;=============================================================================
;; reflexive and transitive closure

(define ((repeated →) ς #:limit [limit #f])
  (define-monad (NondetT (StateT PowerO ID)))
  (define (search ς limit)
    (if (and limit (<= limit 0))
      (return ς)
      (do sΣ′ ≔ (→ ς)
          sΣ ← get
          (cond
            [(∅? sΣ′) (return ς)]
            [(⊆ sΣ′ sΣ) mzero]
            [(do (for/monad+ ([ς′ (set-subtract sΣ′ sΣ)])
                   (do (put (set-add sΣ ς′))
                       (search ς′ (if limit
                                    (sub1 limit)
                                    #f)))))]))))
  (run-StateT (set ς) (search ς limit)))

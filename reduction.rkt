#lang racket/base
(require (for-syntax racket/base syntax/parse
                     (only-in racket/syntax format-id)
                     (only-in racket/list check-duplicates)
                     (only-in racket/match match match-define)
                     (only-in syntax/stx stx-map)
                     (only-in "set.rkt" set list→set set→list ∈ ∪))
         (only-in racket/unit
                 define-signature unit import export link
                 compound-unit invoke-unit)
         (only-in "set.rkt" set ∅? ⊆ set-add set-subtract)
         (only-in "transformers.rkt"
                  PowerO run-StateT define-monad with-monad
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
                         (~optional (~seq #:super [(sname:id sarg ...) ...])
                                    #:name "#:super option")
                         (~optional (~seq #:import [sig-spec ...])
                                    #:name "#:import option")
                         (~optional (~seq #:do [do-body ...])
                                    #:name "#:do option"))
                   ...)
             #:with monad     #'(~? m                 #f)
             #:with mrun      #'(~? mr                #f)
             #:with sup-names  #'(~? (sname ...)      ())
             #:with sup-argss  #'(~? ((sarg ...) ...) ())
             #:with imports   #'(~? (sig-spec ...)    ())
             #:with do-bodies #'(~? (do-body ...)     ())))

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
      (reduction-desc mrun import-sig-stx inst-xformer)
      ((syntax-local-value rid)))

    (syntax-parse
        ;; both can work
        ;; (inst-xformer #`(#,@args ς))
        (syntax-local-apply-transformer inst-xformer rid 'expression #f
                                        #`(#,@args ς))
      #:datum-literals [let nondet-match]
      ;; NOTE: this let form must be consistent with inst-xformer below
      [(let ()
         (define _ M)
         (nondet-match _ _ #:do [do-body ...] rule ...))
       #`(M
          #,mrun
          #,import-sig-stx
          (rule ...)
          (do-body ...))]))

  (define (get-supers-info orig-stx rids argss)
    (define (merge-M Ms)
      (match (list→set (syntax->datum Ms))
        [(set _) (car (syntax->list Ms))]
        [_ (raise-syntax-error
            #f "inconsistent monad specs" orig-stx Ms)]))
    (define (merge-mrun mruns)
      (car (syntax->list mruns)))
    (define (merge-imports importss) ;; TODO: check duplicates?
      (set→list (apply ∪ (stx-map (compose1 list→set syntax->list) importss))))
    (define (merge-rules ruless)
      (syntax-parse ruless
        [(((~and rule (_ _ _ rnam _ ...)) ...) ...)
         (cond
           [(check-duplicates (map syntax-e (syntax->list #'(rnam ... ...))))
            => (λ (rnam) (raise-syntax-error
                          #f (format "duplicate rule ~s" rnam)
                          orig-stx ruless))]
           [else #'(rule ... ...)])]))
    (define (merge-do-bodies do-bodiess) ;; TODO: do something?
      (syntax-parse do-bodiess
        [((do-body ...) ...)
         #'(do-body ... ...)]))

    (if (null? (syntax->list rids))
      #'(#f #f () () ())  ;; (M mrun imports rules do-bodies)
      (cond
        [(check-duplicate-identifier (syntax->list rids))
         => (λ (id) (raise-syntax-error
                     #f (format "duplicate super name ~s" (syntax-e id))
                     orig-stx rids))]
        [else (with-syntax ([((M mrun imports rules do-bodies) ...)
                             (stx-map inst-reduction-info rids argss)])
                (list (merge-M         #'(M ...))
                      (merge-mrun      #'(mrun ...))
                      (merge-imports   #'(imports ...))
                      (merge-rules     #'(rules ...))
                      (merge-do-bodies #'(do-bodies ...))))])))

  (define (derive-mrun M)
    (syntax-parse M
      #:literals (ID ReaderT WriterT StateT FailT NondetT ReduceM)
      [ID
       #:with (m) (generate-temporaries #'(m))
       #'(λ (m) m)]
      [ReduceM
       #:with (m) (generate-temporaries #'(m))
       #'(λ (m) m)]
      [(ReaderT M′)
       #:with (λ (p ...) b) (derive-mrun #'M′)
       #:with (r) (generate-temporaries #'(r))
       #'(λ (r p ...) (run-ReaderT r ((λ (p ...) b) p ...)))]
      [(WriterT _ M′)
       (derive-mrun #'M′)]
      [(StateT _ M′)
       #:with (λ (p ...) b) (derive-mrun #'M′)
       #:with (s) (generate-temporaries #'(s))
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
           (define overridden?
             (let ([rnams (list→set (syntax->datum #'(rnam ...)))])
               (syntax-parser
                 [(_ _ _ rnam _ ...)
                  (∈ (syntax-e #'rnam) rnams)])))]

     #:with (M-of-super
             mrun-of-super
             imports-of-super
             rules-of-super
             do-bodies-of-super) (get-supers-info
                                  stx
                                  #'opts.sup-names
                                  #'opts.sup-argss)

     #:with M (if (syntax-e #'opts.monad)
                #'opts.monad
                (if (syntax-e #'M-of-super)
                  #'M-of-super
                  #'ReduceM))

     #:with mrun (cond
                   [(syntax-e #'opts.mrun) #'opts.mrun]
                   [(syntax-e #'opts.monad) (derive-mrun #'M)]
                   [(syntax-e #'mrun-of-super) #'mrun-of-super]
                   [else (derive-mrun #'M)])

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
     
     #:with M′ (format-id #'rid "~a" (gensym 'M))
     #:with inst-xformer (escape-elipsis
                          #'(λ (stx)
                              (syntax-parse stx
                                [(param ... ς)
                                 ;; NOTE: this let form must be consistent
                                 ;; with inst-reduction-info above
                                 #'(let ()
                                     (define M′ M)
                                     (nondet-match
                                      M′ ς
                                      #:do [do-body ...]
                                      rule ...))])))
     #'(begin
         (define-syntax rid
           (let ([rdesc (reduction-desc #'mrun #'imports inst-xformer)])
             (case-λ
              [() rdesc] ;; called at compile-time
              [(stx) (syntax-parse stx
                       [(_ arg (... ...))
                        #'(inst-reduction rid arg (... ...))])]))))]))

;;=============================================================================
;; inst-reduction

(define-syntax (inst-reduction stx)
  (syntax-parse stx
    [(_ rid:id arg ...)
     #:do [(match-define
             (reduction-desc mrun import-sigs inst-xformer)
             ((syntax-local-value #'rid)))]
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

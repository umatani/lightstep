#lang racket/base
(require (for-syntax (for-syntax racket/base)
                     racket/base syntax/parse
                     (only-in racket/syntax format-id)
                     (only-in racket/list check-duplicates)
                     (only-in racket/match match match-define)
                     (only-in syntax/stx stx-map)
                     (only-in "set.rkt" [-make set]
                              [←list set←list] [→list set→list] [-∈ ∈] [-∪ ∪])
                     ;; racket/pretty
                     )
         (prefix-in r: racket/set)
         (only-in racket/unit
                  define-signature unit import export link
                  compound-unit invoke-unit)
         (only-in racket/match match match-define)
         (only-in "set.rkt" [-make set] [-∅ ∅] [-∅? ∅?] [-⊆ ⊆] [-∪ set-∪]
                  [-∈ set-∈]
                  [-map set-map] [←list set←list] [-for/set for/set]
                  [-add set-add] [-subtract set-subtract])
         (only-in "transformers.rkt"
                  PowerO run-StateT define-monad with-monad
                  ID ReaderT WriterT StateT FailT NondetT)
         (only-in "nondet.rkt" NondetM nondet-match))
(provide ReduceM define-reduction repeated reducer-of mrun-of red^
         (for-syntax options gen-rname escape-elipsis))

(define ReduceM NondetM)

;;=============================================================================
;; define-reduction

(begin-for-syntax
  
  (define-splicing-syntax-class options
    (pattern (~seq (~alt (~optional (~seq #:monad monad)
                                    #:name "#:monad option"
                                    #:defaults ([monad #'#f]))
                         (~optional (~seq #:mrun mrun)
                                    #:name "#:mrun option"
                                    #:defaults ([mrun #'#f]))
                         (~optional (~seq #:super [(sup-name:id sup-arg ...)
                                                   ...])
                                    #:name "#:super option"
                                    #:defaults ([(sup-name 1) '()]
                                                [(sup-arg  2) '()]))
                         (~optional (~seq #:import [import ...])
                                    #:name "#:import option"
                                    #:defaults ([(import 1) '()]))
                         (~optional (~seq #:do [do-body ...])
                                    #:name "#:do option"
                                    #:defaults ([(do-body 1) '()])))
                   ...)))

  (define (gen-rname stx sym)
    (datum->syntax stx (symbol->string (gensym sym))))

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
                                        #`(#,rid #,@args ς))
      #:datum-literals [define let nondet-match]
      ;; NOTE: this let form must be consistent with inst-xformer below
      [(let ()
         (define M′ M)
         (nondet-match _ _ #:do [do-body ...] rule ...))
       #`(M
          #,mrun
          #,import-sig-stx
          (rule ...)
          (do-body ...))]))

  (define (get-supers-info orig-stx rids argss)
    (define (merge-M Ms)
      (match (set←list (syntax->datum Ms))
        [(set _) (car (syntax->list Ms))]
        [_ (raise-syntax-error
            #f "inconsistent monad specs" orig-stx Ms)]))
    (define (merge-mrun mruns)
      (car (syntax->list mruns)))
    (define (merge-imports importss) ;; TODO: check duplicates?
      (set→list (apply ∪ (stx-map (compose1 set←list syntax->list) importss))))
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
  (syntax-parse stx
    [(_ (rid:id param:id ...)
        opts:options
        [pat body ... (~and e (~not :string))
             (~optional rnam:string #:defaults ([rnam (gen-rname #'rid 'r)]))]
        ...)
     #:do [(define (rescope stx)
             (replace-lexical-context #'rid stx))
           (define overridden?
             (let ([rnams (set←list (syntax->datum #'(rnam ...)))])
               (syntax-parser
                 [(_ _ _ rnam _ ...)
                  (∈ (syntax-e #'rnam) rnams)])))]

     #:with (sup-rid ...) #'(opts.sup-name ...)

     #:with (M-of-super
             mrun-of-super
             imports-of-super
             rules-of-super
             do-bodies-of-super) (get-supers-info
                                  stx
                                  #'(sup-rid ...)
                                  #'((opts.sup-arg ...) ...))

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
                                        #,@#'(opts.import ...)))

     #:with (sup-rule ...) (let ([rnams (set←list
                                         (syntax->datum #'(rnam ...)))])
                             (filter (compose1 not overridden?)
                                     (syntax->list #'rules-of-super)))

     #:with (rule ...) (stx-map rescope
                                #'(sup-rule
                                   ...
                                   [pat _ ≔ rnam body ... e]
                                   ...))

     #:with (do-body ...) (stx-map rescope
                                   #`(#,@#'do-bodies-of-super
                                      #,@#'(opts.do-body ...)))
     
     #:with M′ (format-id #'rid "~a" (gensym 'M))
     #:with inst-xformer (escape-elipsis
                          #'(λ (stx)
                              (syntax-parse stx
                                [(self param ... ς)
                                 (let-syntax
                                     ;; shwdows rid macro with reducer (self) 
                                     ([rid (make-rename-transformer #'self)]
                                      [sup-rid (make-rename-transformer #'self)]
                                      ...)
                                   ;; NOTE: this let form must be consistent
                                   ;; with inst-reduction-info above
                                   #'(let ()
                                       (define M′ M)
                                       (nondet-match
                                        M′ ς
                                        #:do [do-body ...]
                                        rule ...)))])))

     ;; #:do [(pretty-print (syntax->datum #'inst-xformer))]

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

(define-signature red^ (mrun reducer))

(define-syntax (inst-reduction stx)
  (syntax-parse stx
    [(_ rid:id arg ...)
     #:do [(match-define
             (reduction-desc mrun import-sigs inst-xformer)
             ((syntax-local-value #'rid)))]
     #:with (body ...) #`((import #,@import-sigs)
                          (export red^)
                          (define (reducer ς)
                            #,(inst-xformer #'(reducer arg ... ς)))
                          (define mrun #,mrun)
                          (values mrun reducer))
     ;; TODO: invoke-unit with import-sig-specs?
     ;;   to construct parameterized unit instances
     (if (null? (syntax->list import-sigs))
       #'(invoke-unit (unit body ...))
       #'(unit body ...))]))

;;=============================================================================
;; reflexive and transitive closure

;; TODO: #:trace option
;;   return 𝒫(List(ς)) instead of 𝒫(ς)
;; TODO: ->graph function
;;   from traces, construct the overall graph in the ς space
;;   it is better to label each edge with rname

(struct Queueof (head tail) #:transparent #:mutable
  #:constructor-name Queue)

(define (make-queue) (Queue '() '()))

(define (queue-empty? q)
  (and (null? (Queueof-head q)) (null? (Queueof-tail q))))

(define (enqueue! q a)
  (set-Queueof-tail! q (cons a (Queueof-tail q))))

(define (dequeue! q)
  (when (queue-empty? q)
    (error 'dequeue! "queue is empty"))
  (when (null? (Queueof-head q))
    (set-Queueof-head! q (reverse (Queueof-tail q)))
    (set-Queueof-tail! q '()))
  (begin0
      (car (Queueof-head q))
    (set-Queueof-head! q (cdr (Queueof-head q)))))

(define ((repeated →) ς-init #:limit [limit #f])
  (define wl (make-queue))
  (define immutables (r:mutable-set))
  (define Σ (r:mutable-set))

  (define (search)
    (if (queue-empty? wl)
      Σ
      (let* ([x (dequeue! wl)])
        (match-define (cons limit current) x)
        (if (and limit (<= limit 0))
          (r:set-add! immutables current)
          (let ([nexts (→ current)])
            (if (∅? nexts)
              (r:set-add! immutables current)
              (for ([ς′ nexts]
                    #:unless (r:set-member? Σ ς′))
                (enqueue! wl (cons (and limit (sub1 limit)) ς′))
                (r:set-add! Σ ς′)))))
        (search))))
  (enqueue! wl (cons limit ς-init))
  (r:set-add! Σ ς-init)
  (search)
  (cons (for/set ([ς immutables]) ς) (for/set ([ς Σ]) ς)))

;;;; obsolete (problematic)

(define ((repeated′ →) ς #:limit [limit #f])
  (define-monad (StateT PowerO ID))
  (define (step ς)
    (do ςs′ ≔ (→ ς)
        (if (∅? ςs′)
          (return 'done)
          (return ςs′))))
  (define (loop ςs dones)
    (match ςs
      [(set) (return dones)]
      [(set (cons limit ς) ςs′ ...)
       (if (and limit (<= limit 0))
         (loop ςs′ (set-add dones ς))
         (do x ← (step ς)
             (match x
               ['done (loop ςs′ (set-add dones ς))]
               [ςs″
                (do sΣ ← get
                    (loop (set-∪ ςs′
                                 (for/set ([ς″ ςs″]
                                           #:unless (set-∈ ς″ sΣ))
                                   (put (set-add sΣ ς″))
                                   (cons (and limit (sub1 limit)) ς″)))
                          dones))])))]))
  (run-StateT (set ς) (loop (set (cons limit ς)) ∅)))

;;=============================================================================
;; shortcuts

(define-syntax-rule (reducer-of x)
  (let-values ([(mrun reducer) x])
    reducer))

(define-syntax-rule (mrun-of x)
  (let-values ([(mrun reducer) x])
    mrun))

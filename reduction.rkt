#lang racket/base
(require (for-syntax racket/base syntax/parse
                     (only-in racket/match match-define)
                     (only-in syntax/stx stx-map)
                     (only-in "set.rkt" list→set ∈))
         (only-in racket/unit
                  define-signature unit import export link
                  compound-unit invoke-unit)
         (only-in racket/match match)
         (only-in "set.rkt" ∅ ∅? ∈ set set-add)
         (only-in "transformers.rkt"
                  PowerO ID StateT FailT NondetT define-monad with-monad
                  run-StateT)
         (only-in "reduction/bindings.rkt" ReduceT))
(provide define-reduction inst-reduction apply-reduction*)


;;=============================================================================
;; nondet-match

;(define (ReduceT M) (FailT (NondetT M)))

(define-syntax (nondet-match stx)
  (syntax-parse stx
    [(_ x #:default dclause [pat body ... e] ...)
     #:with nexts #'(with-monad (ReduceT ID)
                      (mconcat (match x
                                 [pat (do body ... (return e))]
                                 [_ mzero])
                               ...))
     (if (syntax-e #'dclause)
       (with-syntax ([[pat body ... e] #'dclause])
         #'(let ([ςs nexts])
             (if (∅? ςs)
               (with-monad (ReduceT ID)
                 (match x
                   [pat (do body ... (return e))]
                   [_ mzero]))
               ςs)))
       #'nexts)]
    [(_ x [pat body ... e] ...)
     #'(nondet-match x #:default #f [pat body ... e] ...)]))

(module+ test ;;test-nondet-match
  (require rackunit)

  (check-equal? (nondet-match '(1 2 3)
                              [x x]
                              [(list a b c) (+ a b c)])
                (set 6 '(1 2 3)))
  
  (check-equal? (nondet-match (set 1 2 3)
                              [x x]
                              [(set a b c) (set (set a b) c)]
                              [(set a ...) (apply + a)])
                (set (set 1 (set 2 3)) (set 1 3 2) 6))

  (check-equal? (nondet-match (set 1 2 3)
                              [x (nondet-match x [(set a b c)
                                                  (set (set a b) c)])]
                              [x (nondet-match x [(set a ...) (apply + a)])])
                (set (set 6) (set (set 1 (set 2 3)))))
  (check-equal? (nondet-match '(1 2 3)
                              [`(,x ...) x])
                (set '(1 2 3)))

  (check-equal? (nondet-match '(1 2 3)
                              [(list a b) (+ a b)])
                ∅)
  (check-equal? (nondet-match '(1 2 3)
                              #:default [xs xs]
                              [(list a b) (+ a b)])
                (set '(1 2 3)))
  (check-equal? (nondet-match '(1 2 3)
                              #:default [xs xs]
                              [(list a b c) (+ a b c)])
                (set 6)))

;;=============================================================================
;; define-reduction

(begin-for-syntax
  (define-splicing-syntax-class options
    (pattern (~seq (~alt (~optional (~seq #:super (sname:id sarg ...))
                                    #:name "#:super option")
                         (~optional (~seq #:import [sig-spec ...])
                                    #:name "#:import option")
                         (~optional (~seq #:do [do-body ...])
                                    #:name "#:do option")
                         (~optional (~seq #:default [pat body ... e])
                                    #:name "#:default option")) ...)
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

  (struct reduction-desc (import-sig expander))

  (define (inst-reduction-info rid args)
    (match-define
      (reduction-desc import-sig-stx expander-stx)
      (syntax-local-value rid))

    (define def-cxt (syntax-local-make-definition-context))
    (syntax-local-bind-syntaxes (list #'expander)
                                (escape-elipsis expander-stx) def-cxt)

    (syntax-parse (local-expand #`(expander #,@args ς)
                                'expression
                                (list #'nondet-match)
                                def-cxt)
      #:datum-literals [let-values nondet-match]
      [(let-values () do-body ... (nondet-match _ #:default drule rule ...))
       #`(#,import-sig-stx
          (rule ...)
          (do-body ...)
          drule)])))


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
                                do-body ...
                                (nondet-match ς
                                              #:default default-clause
                                              rule ...))]))
     
     #'(define-syntax rid (reduction-desc #'imports #'expander))]))

;;=============================================================================
;; inst-reduction

(define-syntax (inst-reduction stx)
  (syntax-parse stx
    [(_ rid:id arg ...)
     #:do [(match-define
             (reduction-desc import-sigs expander-stx)
             (syntax-local-value #'rid))]

     #`(unit
         (import #,@import-sigs) (export)

         (define-signature M^
           ((define-syntaxes (inst) #,(escape-elipsis expander-stx))))

         (invoke-unit
          (compound-unit (import) (export)
           (link (([m : M^]) (unit (import) (export M^)))
                 (() (unit (import M^) (export)
                       (define (reducer ς) (inst arg ... ς))
                       reducer)
                     m)))))]))

;;=============================================================================
;; apply-reduction*

(define (apply-reduction* → ς)
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

#lang racket
(require lightstep/reduction lightstep/set
         (only-in "design3.rkt" EC))

(module+ test (require rackunit))

;;;; ユニット連携

;;;; (a) 多くの補助定義に依存する
;;;; (b) 相互依存している(補助定義が定義しているreductionに依存している)
;;;; (c) コンパイル時ではなく，**実行時に**モジュールの取り替えが可能．
;;;;     とりわけ，システム全体で同じ言語の多数のバリエーションが複数
;;;;     コンポーネント毎に必要なときなどに便利

;; (1) これまでの補助手続きすべてをユニット化 + δユニット

;;  まずは，δユニットのコードでunitの基本説明

(define-signature delta^
  (prim? δ))

(define-unit delta1@
  (import)
  (export delta^)

  (define (prim? op)
    (member op '(+ <=)))

  (define (δ op vs)
    (case op
      [(+)  (apply +  vs)]
      [(<=) (apply <= vs)])))

(define-signature misc^
  (val? subst))

(define-unit misc1@
  (import delta^)
  (export misc^)

  (define (val? x)
    (match x
      [(? number?)  #t]
      [(? boolean?) #t]
      [`(λ (,x) ,e) #t]
      [_            #f]))

  ;; as before
  (define (subst e x e′)
    (match e
      [(? symbol? y) (if (eq? x y) e′ e)]
      [`(λ (,(? symbol? y)) ,e₁)
       (if (eq? x y)
         `(λ (,y) ,e₁)
         (let ([y-new (gensym y)])
           `(λ (,y-new) ,(subst (subst e₁ y y-new) x e′))))]
      [(? val? v) v]
      [`(,(? prim? op) ,e₁ ,e₂)
       `(,op ,(subst e₁ x e′) ,(subst e₂ x e′))]
      [`(if ,e₁ ,e₂ ,e₃)
       `(if ,(subst e₁ x e′) ,(subst e₂ x e′) ,(subst e₃ x e′))]
      [`(fix ,e) `(fix ,(subst e x e′))]
      [`(,e₁ ,e₂) `(,(subst e₁ x e′) ,(subst e₂ x e′))])))

(define-reduction (-->PCF₇-rule -->)
  #:import (delta^ misc^)
  [`(,(? prim? op) ,(? val? vs) ...)
   (δ op vs) "prim"]
  [`((λ (,x) ,e) ,(? val? v)) (subst e x v) "β"]
  [`(if #f ,e₂ ,e₃) e₃ "if-false"]
  [`(if ,e₁ ,e₂ ,e₃)
   #:when (and (val? e₁) (not (false? e₁)))
   e₂ "if-true"]
  [`(fix (λ (,x) ,e))
   y ≔ (gensym 'y)
   `((λ (,x) ,e) (λ (,y) ((fix (λ (,x) ,e)) ,y)))
   "fix"]
  [(EC e)
   e′ ← (--> e)
   (EC e′)
   "EC"])

(module+ test
  (printf "----- PCF₇ ------------\n")
  (define -->PCF₇ (letrec ([u1 (inst-reduction -->PCF₇-rule r1)]
                           [r1 (invoke-unit
                                (compound-unit (import) (export)
                                 (link (([d : delta^]) delta1@)
                                       (([m : misc^ ]) misc1@ d)
                                       (() u1 m d))))])
                    r1))

  (check-equal? (car (apply-reduction* -->PCF₇ '(+ 1 2))) (set 3))
  (check-equal? (car (apply-reduction* -->PCF₇ '(+ (+ 1 2) 3))) (set 6))
  (check-equal? (car (apply-reduction* -->PCF₇ '(+ (+ 1 2) (+ 3 (+ 7 5)))))
                (set 18))
  (check-equal? (car (apply-reduction* -->PCF₇ '(<= 1 2))) (set #t))
  (check-equal? (car (apply-reduction* -->PCF₇ '(<= 3 2))) (set #f))
  (check-equal? (car (apply-reduction* -->PCF₇ '(if #f 3 2))) (set 2))
  (check-equal? (car (apply-reduction* -->PCF₇ '(if #t 3 2))) (set 3))
  (check-equal? (car (apply-reduction* -->PCF₇ '(if 8 3 2))) (set 3))
  (check-equal? (car (apply-reduction* -->PCF₇ '(if (<= 10 8) 3 2))) (set 2))
  (check-equal? (car (apply-reduction* -->PCF₇ '(if (+ 10 8) 3 2))) (set 3))
  (check-equal? (car (apply-reduction* -->PCF₇ '(if (<= 10 108) 3 2)))
                (set 3))
  (check-equal?
   (car (apply-reduction* -->PCF₇ '(if (if (<= 10 108) #f #t)
                                     (+ (+ 1 2) 3)
                                     (+ (+ 1 2) (+ 3 (+ 7 5))))))
   (set 18))
  (check-equal?
   (car (apply-reduction* -->PCF₇ '(((if (if (<= 10 108) #f #t)
                                       (λ (x) (λ (y) x))
                                       (λ (x) (λ (y) y))) 1) 2)))
   (set 2))
  (check-equal?
   (car (apply-reduction* -->PCF₇ '(((if (if (<= 108 10) #f #t)
                                       (λ (x) (λ (y) x))
                                       (λ (x) (λ (y) y))) 1) 2)))
   (set 1))
  #;
  (check-equal?
   (apply-reduction* -->PCF₇ '(fix ((λ (x) x) (λ (y) y))))
   (set '(λ (y2845333) ((fix (λ (y) y)) y2845333))))
  (check-equal? (car (apply-reduction* -->PCF₇ '((λ (x) x) 2))) (set 2))
  (check-equal? (car (apply-reduction* -->PCF₇ '((λ (x) 1) 2))) (set 1))
  (check-equal? (car (apply-reduction* -->PCF₇ '((λ (x) #t) 2))) (set #t))
  (check-equal? (car (apply-reduction* -->PCF₇ '((λ (x) (+ x 1)) 2)))
                (set 3))
  (check-equal? (car (apply-reduction* -->PCF₇ '((λ (x) (<= 1 x)) 2)))
                (set #t))
  (check-equal? (car (apply-reduction* -->PCF₇ '((λ (x) (if x x 0)) 2)))
                (set 2))
  #;
  (check-equal? (apply-reduction* -->PCF₇ '((λ (x) (fix x)) (λ (y) y)))
                (set '(λ (y2904847) ((fix (λ (y) y)) y2904847)))))

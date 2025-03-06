#lang racket
(require (for-syntax syntax/parse)
         lightstep/base
         (only-in racket/random random-ref)
         (only-in "design1.rkt" val? cxt))
(provide subst ECxt -->PCF₅-rule)

(module+ test (require rackunit))

;;;;;;;;;; 拡張性のためのさらなる機能(つづき)

;;;;    (2) ≔ を ← にするためのパラメタライズ．実用例は？
;;;;      (1)のようにあるreduction定義のcontextが1つの特定の名前セットを
;;;;      形成しているならいいが，≔ や ← のように，切り替えたい機能の複数が
;;;;      別の名前で重複してcontext中で可視な場合，それらの間での切り替えは
;;;;      不可能．そのような場合には，(2)の方が扱いやすい．
;;;;        ≔ を ← に変更したいような例．metafunctionがsetを返すように変わる
;;;;        ような応用

;;;; ambを追加して非決定計算へ拡張
;;  まずはベースを1から再構築．
;;  (a) ≔ を2種類に分割
;;  (b) ≔<1>, ≔<2>, --> をパラメータ化

(define (subst e x e′)
  (match e
    [(? number? n) n]
    [(? boolean? b) b]
    [`(+ ,e₁ ,e₂)
     `(+ ,(subst e₁ x e′) ,(subst e₂ x e′))]
    [`(<= ,e₁ ,e₂)
     `(<= ,(subst e₁ x e′) ,(subst e₂ x e′))]
    [`(if ,e₁ ,e₂ ,e₃)
     `(if ,(subst e₁ x e′) ,(subst e₂ x e′) ,(subst e₃ x e′))]
    [`(fix ,e) `(fix ,(subst e x e′))]

    [(? symbol? y) (if (eq? x y) e′ e)]
    [`(λ (,(? symbol? y)) ,e₁)
     (if (eq? x y)
       `(λ (,y) ,e₁)
       (let ([y′ (gensym y)])
         `(λ (,y′) ,(subst (subst e₁ y y′) x e′))))]
    [`(,e₁ ,e₂) `(,(subst e₁ x e′) ,(subst e₂ x e′))]
    [`(amb ,es ...) `(amb ,@(map (λ (e) (subst e x e′)) ;; NEW
                                 es))]))

(define-match-expander ECxt
  (syntax-parser
    [(ECxt p)
     #'(cxt ECxt p
            `(+ ,(? val? v) □)
            `(+ □ ,e₁)
            `(<= ,(? val? v) □)
            `(<= □ ,e₁)
            `(if □ ,e₁ ,e₂)
            `(fix □)
            `(,(? val? v) □)
            `(□ ,e₁))]))

(define (select es)
  (random-ref es))

(define-reduction (-->PCF₅-rule --> ≔<1> ≔<2>)
  [`((λ (,x) ,e) ,(? val? v)) (subst e x v) "β"]
  [`(+ ,(? number? n₁) ,(? number? n₂)) (+ n₁ n₂) "add"]
  [`(<= ,(? number? n₁) ,(? number? n₂))
   n ≔<1> (<= n₁ n₂)
   n "le"]
  [`(if #f ,e₂ ,e₃) e₃ "if-false"]
  [`(if ,e₁ ,e₂ ,e₃)
   #:when (and (val? e₁) (not (false? e₁)))
   e₂ "if-true"]
  [`(fix (λ (,x) ,e))
   y ≔<1> (gensym 'y)
   `((λ (,x) ,e) (λ (,y) ((fix (λ (,x) ,e)) ,y)))
   "fix"]
  [`(amb ,es ...)
   e′ ≔<2> (select es)
   e′
   "amb"]
  [(ECxt e)
   e′ ← (--> e)
   (ECxt e′)
   "EC"])

;; One benefit of parameterization over non-lexical extension is ...
(define-values (-->PCF₅ reducer-PCF₅)
  (call-with-values
   (λ () (-->PCF₅-rule reducer-PCF₅ ≔ ≔))
   (λ (mrun reducer) (values (compose1 mrun reducer) reducer))))
(define -->>PCF₅ (repeated -->PCF₅))

(module+ test
  ;(printf "----- PCF₅ ------------\n")
  (check-not-exn (λ () (-->>PCF₅ '(amb 1 2 3 4 5))))
  (check-not-exn (λ () (-->>PCF₅ '(+ (amb 1 2 3 4) (amb 10 20 30 40))))))

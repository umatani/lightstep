#lang racket
(require lightstep/base
         (for-syntax syntax/parse syntax/stx))
(provide -->PCF₃-rule -->₂-rule val? subst ECxt cxt)

(module+ test (require rackunit))

;;;;;;;;;; 基本機能

;; rule setの書き方の基本
;;   Racket 標準の match の pattern をそのまま利用可能
(define-reduction (-->₀-rule)
  [(cons x y) x "car"])

;; parameterized rule set のため (引数ありは後述2)
(define-values (mrun₀ reducer₀) (-->₀-rule))
(define -->₀ (compose1 mrun₀ reducer₀))

(module+ test
  ;(printf "---- cons -------------\n")
  ;; reducer とは (-> state (Setof state))
  (check-equal? (-->₀ (cons 1 2)) (set 1))

  ;; apply-reduction-relation* は multi-step
  ;;   set of irreducible term を返す
  ;;   irreducible = どのルールにもマッチしなかった state
  (check-equal? (-->₀ (cons (cons 1 2) 3)) (set '(1 . 2)))

  (check-equal?
   (car ((repeated -->₀) (cons (cons 1 2) 3)))
   (set 1)))

;; 非決定的である例
(define-reduction (-->₁-rule)
  [(cons x y) x "car"]
  [(cons x y) y "cdr"])

(define-values (mrun₁ reducer₁) (-->₁-rule))
(define -->₁ (compose1 mrun₁ reducer₁))

(module+ test
  (check-equal? (-->₁ (cons (cons 1 2) 3)) (set 3 '(1 . 2)))

  (check-equal? (car ((repeated -->₁) (cons (cons 1 2) 3)))
                (set 1 2 3)))

;; 例：ここまでの機能で untyped pure λ-calculus の β

; subst : e x e -> e
(define (subst e x e′)
  (match e
    [(? symbol? y) (if (eq? x y) e′ e)]
    [`(λ (,(? symbol? y)) ,e₁)
     (if (eq? x y)
       `(λ (,y) ,e₁)
       (let ([y′ (gensym y)])
         `(λ (,y′) ,(subst (subst e₁ y y′) x e′))))]
    [`(,e₁ ,e₂) `(,(subst e₁ x e′) ,(subst e₂ x e′))]))

(define-reduction (-->LAM₀-rule)
  [`((λ (,x) ,e₁) ,e₂) (subst e₁ x e₂) "β"])

(define-values (mrun-LAM₀ reducer-LAM₀) (-->LAM₀-rule))
(define -->LAM₀ (compose1 mrun-LAM₀ reducer-LAM₀))
(define -->>LAM₀ (repeated -->LAM₀))

(module+ test
  ;(printf "---- LAM₀ -------------\n")
  ;; 下と一緒
  ;; (-->LAM₀ '((λ (x) x) (λ (z) (z z))))
  ;; (-->LAM₀ '((λ (x) (λ (z) (x z))) (λ (z) (x z))))
  (check-equal?
   (car (-->>LAM₀ '((λ (x) x) (λ (z) (z z)))))
   (set '(λ (z) (z z))))

  #;
  (check-equal?
   (-->>LAM₀ '((λ (x) (λ (z) (x z))) (λ (z) (x z))))
   (set '(λ (z685121) ((λ (z) (x z)) z685121))))

  (check-equal?
   (-->LAM₀ '((λ (x) (x x)) (λ (z) (z z))))
   (set '((λ (z) (z z)) (λ (z) (z z)))))
  ;; cycleもちゃんと検出
  (check-equal?
   (car (-->>LAM₀ '((λ (x) (x x)) (λ (z) (z z)))))
   (set)))

;;;; PCF に移行して reduction の拡張
;;;; ruleの中に書ける複数式の説明．通常の式以外に ≔ や #:when
;;;; ここで reduction の拡張も説明．

(define-reduction (-->PCF₀-rule) #:super [(-->LAM₀-rule)]
  [`(+ ,(? number? n₁) ,(? number? n₂))
   (+ n₁ n₂) "add"]
  [`(<= ,(? number? n₁) ,(? number? n₂))
   n ≔ (<= n₁ n₂)
   n "le"]
  [`(if #f ,e₂ ,e₃) e₃ "if-false"]
  [`(if ,e₁ ,e₂ ,e₃)
   #:when (not (false? e₁))
   e₂ "if-true"]
  [`(fix (λ (,x) ,e))
   y ≔ (gensym 'y)
   `((λ (,x) ,e) (λ (,y) ((fix (λ (,x) ,e)) ,y)))
   "fix"])

(define-values (mrun-PCF₀ reducer-PCF₀) (-->PCF₀-rule))
(define -->PCF₀ (compose1 mrun-PCF₀ reducer-PCF₀))
(define -->>PCF₀ (repeated -->PCF₀))

(module+ test
  ;(printf "---- PCF₀ -------------\n")
  ;; superの機能維持
  (check-equal?
   (car (-->>PCF₀ '((λ (x) x) (λ (z) (z z)))))
   (set '(λ (z) (z z))))
  #;
  (check-equal?
   (-->>PCF₀ '((λ (x) (λ (z) (x z))) (λ (z) (x z))))
   (set '(λ (z787758) ((λ (z) (x z)) z787758))))
  ;;
  (check-equal? (-->PCF₀ '(+ 1 2)) (set 3))
  (check-equal? (-->PCF₀ '(+ (+ 1 2) 3)) (set)) ;; これはまだ(eval cxtが必要)
  (check-equal? (-->PCF₀ '(<= 1 2)) (set #t))
  (check-equal? (-->PCF₀ '(<= 3 2)) (set #f))
  (check-equal? (-->PCF₀ '(if #f 3 2)) (set 2))
  (check-equal? (-->PCF₀ '(if #t 3 2)) (set 3))
  (check-equal? (-->PCF₀ '(if 8 3 2)) (set 3))
  (check-equal? (-->PCF₀ '(if (<= 10 8) 3 2)) (set 3)) ;; これもまだ
  #;
  (check-equal? (-->PCF₀ '(fix (λ (x) x)))
                (set '((λ (x) x) (λ (y986678) ((fix (λ (x) x)) y986678)))))
  )

;;;; 実際には，rule body は nondet monad．← (bind)がある．
;;;;   別の遷移を埋め込める．
;;; 例：λ-calculus の evaluation context (Redexでは特別な記法)

(define-reduction (-->PCF₁-rule)
  [`(if ,e₁ ,e₂ ,e₃)
   e₁′ ← (-->PCF₀ e₁)
   `(if ,e₁′ ,e₂ ,e₃)
   "ECif"])

(define-values (mrun-PCF₁ reducer-PCF₁) (-->PCF₁-rule))
(define -->PCF₁ (compose1 mrun-PCF₁ reducer-PCF₁))
(define -->>PCF₁ (repeated -->PCF₁))

(module+ test
  ;(printf "---- PCF₁ -------------\n")
  ;; 継承してないので上4つはできない．
  (check-equal? (car (-->>PCF₁ '(+ 1 2)))
                (set '(+ 1 2)))
  (check-equal? (car (-->>PCF₁ '(+ (+ 1 2) 3)))
                (set '(+ (+ 1 2) 3)))
  (check-equal? (car (-->>PCF₁ '(<= 1 2))) (set '(<= 1 2)))
  (check-equal? (car (-->>PCF₁ '(<= 3 2))) (set '(<= 3 2)))
  (check-equal? (-->PCF₁ '(if #f 3 2)) (set))
  (check-equal? (-->PCF₁ '(if #t 3 2)) (set))
  (check-equal? (-->PCF₁ '(if 8 3 2)) (set))
  (check-equal? (-->PCF₁ '(if (<= 10 8) 3 2)) (set '(if #f 3 2)))
  (check-equal? (car (-->>PCF₁ '(if #f 3 2)))
                (set '(if #f 3 2)))
  (check-equal? (car (-->>PCF₁ '(if #t 3 2)))
                (set '(if #t 3 2)))
  (check-equal? (car (-->>PCF₁ '(if 8 3 2)))
                (set '(if 8 3 2)))
  (check-equal? (car (-->>PCF₁ '(if (<= 10 8) 3 2)))
                (set '(if #f 3 2))))

;; 自分自身を埋め込めることで，evaluation-contextの再帰構造をシンプルに表現できる
;;   if-trueのオーバーライド (val?の追加)

(define (val? x)
  (match x
    [(? number?)  #t]
    [(? boolean?) #t]
    [`(λ (,x) ,e) #t]
    [_            #f]))

(define-reduction (-->PCF₂-rule) #:super [(-->PCF₀-rule)]
  ;; override
  [`((λ (,x) ,e) ,(? val? v))
   (subst e x v) "β"]

  ;; override
  [`(if ,e₁ ,e₂ ,e₃)
   #:when (and (val? e₁) (not (false? e₁)))
   e₂ "if-true"]

  [`(,e₁ ,e₂)
   e₁′ ← (-->PCF₂ e₁)
   `(,e₁′ ,e₂)
   "EC-app1"]

  [`(,(? val? v) ,e)
   e′ ← (-->PCF₂ e)
   `(,v ,e′)
   "EC-app2"]

  [`(+ ,e₁ ,e₂)
   e₁′ ← (-->PCF₂ e₁)
   `(+ ,e₁′ ,e₂)
   "EC-add1"]

  [`(+ ,(? val? v) ,e)
   e′ ← (-->PCF₂ e)
   `(+ ,v ,e′)
   "EC-add2"]

  [`(<= ,e₁ ,e₂)
   e₁′ ← (-->PCF₂ e₁)
   `(<= ,e₁′ ,e₂)
   "EC-le1"]

  [`(<= ,(? val? v) ,e)
   e′ ← (-->PCF₂ e)
   `(<= ,v ,e′)
   "EC-le2"]

  [`(if ,e₁ ,e₂ ,e₃)
   e₁′ ← (-->PCF₂ e₁)
   `(if ,e₁′ ,e₂ ,e₃)
   "EC-if"]

  [`(fix ,e)
   e′ ← (-->PCF₂ e)
   `(fix ,e′)
   "EC-fix"])

(define-values (mrun-PCF₂ reducer-PCF₂) (-->PCF₂-rule))
(define -->PCF₂ (compose1 mrun-PCF₂ reducer-PCF₂))
(define -->>PCF₂ (repeated -->PCF₂))

(module+ test
  ;(printf "----- PCF₂ ------------\n")
  (check-equal? (car (-->>PCF₂ '(+ 1 2))) (set 3))
  (check-equal? (car (-->>PCF₂ '(+ (+ 1 2) 3))) (set 6))
  (check-equal? (car (-->>PCF₂ '(+ (+ 1 2) (+ 3 (+ 4 5)))))
                (set 15))
  (check-equal? (car (-->>PCF₂ '(<= 1 2))) (set #t))
  (check-equal? (car (-->>PCF₂ '(<= 3 2))) (set #f))
  (check-equal? (-->PCF₂ '(if #f 3 2)) (set 2))
  (check-equal? (-->PCF₂ '(if #t 3 2)) (set 3))
  (check-equal? (-->PCF₂ '(if 8 3 2)) (set 3))
  (check-equal? (-->PCF₂ '(if (<= 10 8) 3 2)) (set '(if #f 3 2)))
  (check-equal? (car (-->>PCF₂ '(if #f 3 2))) (set 2))
  (check-equal? (car (-->>PCF₂ '(if #t 3 2))) (set 3))
  (check-equal? (car (-->>PCF₂ '(if 8 3 2))) (set 3))
  (check-equal? (car (-->>PCF₂ '(if (<= 10 8) 3 2))) (set 2))
  (check-equal? (car (-->>PCF₂ '(if (+ 10 8) 3 2))) (set 3))
  (check-equal? (car (-->>PCF₂ '(if (<= 10 108) 3 2)))
                (set 3))
  (check-equal?
   (car (-->>PCF₂ '(if (if (<= 10 108) #f #t)
                                     (+ (+ 1 2) 3)
                                     (+ (+ 1 2) (+ 3 (+ 4 5))))))
   (set 15))
  (check-equal?
   (car (-->>PCF₂ '(((if (if (<= 10 108) #f #t)
                                       (λ (x) (λ (y) x))
                                       (λ (x) (λ (y) y))) 1) 2)))
   (set 2))
  ;; ↓substをオーバーライドしてないから動かない！
  #;
  (car (-->>PCF₂ '(((if (if (<= 108 10) #f #t)
                                      (λ (x) (λ (y) x))
                                      (λ (x) (λ (y) y))) 1) 2)))
  #;
  (check-equal?
   (car (-->>PCF₂ '(fix ((λ (x) x) (λ (y) y)))))
   (set '(λ (y1701765) ((fix (λ (y) y)) y1701765))))
  )

;; 各ルール中に遷移を埋め込むかわりに，eval-cxtマッチエクスパンダーを定義すれば
;; モジュール化．後の subreduction オーバーライドの対象にもできる．

;; (cxt EC pat pred `(if □ ,pat1 ,pat2))
;; ==>
;; (and `(if ,(? pred? pat) ,_ ,_)
;;      (app (match-λ
;;             [`(if ,_ ,pat1 ,pat2)
;;              (λ (e) `(if ,e ,pat1* ,pat2*))]) EC))
;; ってことだけ書けば，次の実際の定義は載せなくていい or 付録？ → ページ数次第

(begin-for-syntax
  (define (mask-unquote stx)
    (syntax-parse stx
      #:datum-literals [unquote ?]
      [(unquote (? p x)) #'(unquote (? p))]
      [(unquote e) #'(unquote _)]
      [(s ...) (stx-map mask-unquote #'(s ...))]
      [s #'s]))
  (define (pick-id stx)
    (syntax-parse stx
      #:datum-literals [unquote ?]
      [(unquote (? p x)) #'(unquote x)]
      [(s ...) (stx-map pick-id #'(s ...))]
      [s #'s]))
  (define-syntax-class hole
    #:attributes (nam pat upat body)
    (pattern (~datum □)
             #:with nam  #'□
             #:with pat  #',_
             #:attr upat (λ (pat) #`,#,pat)
             #:with body #',nam)
    (pattern (e1 ... h:hole e2 ...)
             #:with (u1 ...) (stx-map mask-unquote #'(e1 ...))
             #:with (u2 ...) (stx-map mask-unquote #'(e2 ...))
             #:with (b1 ...) (stx-map pick-id #'(e1 ...))

             #:with (b2 ...) (stx-map pick-id #'(e2 ...))
             #:with nam  #'h.nam
             #:with pat  #'(e1 ... h.pat e2 ...)
             #:attr upat (λ (pat)
                           #`(u1 ... #,((attribute h.upat) pat) u2 ...))
             #:with body #'(b1 ... h.body b2 ...))))

(define-match-expander cxt
  (syntax-parser
    [(_ C:id pat h:hole)
     #`(and #,((attribute h.upat) #'pat)
            (app (match-λ
                   [h.pat (λ (h.nam) h.body)])
                 C))]
    [(_ C:id pat h1:hole h2:hole ...)
     #'(or (cxt C pat h1)
           (cxt C pat h2) ...)]))

;; この定義は載せる
(define-match-expander ECxt
  (syntax-parser
    [(ECxt p)
     #'(cxt ECxt p
        `(+ ,(? val? v) □)
        `(+ □ ,e1)
        `(<= ,(? val? v) □)
        `(<= □ ,e1)
        `(if □ ,e1 ,e2)
        `(fix □)
        `(,(? val? v) □)
        `(□ ,e1))]))

;; ↑は以下に展開される
#;
(define-match-expander ECxt
  (lambda (stx)
    (syntax-case stx ()
      [(ECxt e) #'(or
                   (and `(fix ,e)
                        (app (match-lambda
                               [`(fix ,_)
                                (λ (x) `(fix ,x))]) ECxt))
                   (and `(+ ,(? val?) ,e)
                        (app (match-lambda
                               [`(+ ,(? val? v) ,e)
                                (λ (x) `(+ ,v ,x))]) ECxt))
                   (and `(+ ,e ,_)
                        (app (match-lambda
                               [`(+ ,_ ,e1)
                                (λ (x) `(+ ,x ,e1))]) ECxt))
                   (and `(<= ,(? val?) ,e)
                        (app (match-lambda
                               [`(<= ,(? val? v) ,e)
                                (λ (x) `(<= ,v ,x))]) ECxt))
                   (and `(<= ,e ,_)
                        (app (match-lambda
                               [`(<= ,_ ,e1)
                                (λ (x) `(<= ,x ,e1))]) ECxt))
                   (and `(if ,e ,_ ,_)
                        (app (match-lambda
                               [`(if ,_ ,e1 ,e2)
                                (λ (x) `(if ,x ,e1 ,e2))]) ECxt))
                   (and `(,(? val?) ,e)
                        (app (match-lambda
                               [`(,(? val? v) ,e)
                                (λ (x) `(,v ,x))]) ECxt))
                   (and `(,e ,_)
                        (app (match-lambda
                               [`(,_ ,e1)
                                (λ (x) `(,x ,e1))]) ECxt)))])))

(module+ test
  ;(printf "----- EC ------------\n")
  (check-equal?
   (match '(if (+ 1 2) (+ 3 4) 5)
     [(ECxt e) (ECxt `(<= ,e ,e))])
   '(if (<= (+ 1 2) (+ 1 2)) (+ 3 4) 5)))


(define-reduction (-->PCF₃-rule) #:super [(-->PCF₀-rule)]
  ;; override
  [`((λ (,x) ,e) ,(? val? v))
   (subst e x v) "β"]

  ;; override
  [`(if ,e₁ ,e₂ ,e₃)
   #:when (and (val? e₁) (not (false? e₁)))
   e₂ "if-true"]  

  [(ECxt e)
   e′ ← (-->PCF₃ e)
   (ECxt e′)
   "EC"])

(define-values (mrun-PCF₃ reducer-PCF₃) (-->PCF₃-rule))
(define -->PCF₃ (compose1 mrun-PCF₃ reducer-PCF₃))
(define -->>PCF₃ (repeated -->PCF₃))

(module+ test
  ;(printf "----- PCF₃ ------------\n")
  (check-equal? (car (-->>PCF₃ '(+ 1 2))) (set 3))
  (check-equal? (car (-->>PCF₃ '(+ (+ 1 2) 3))) (set 6))
  (check-equal? (car (-->>PCF₃ '(+ (+ 1 2) (+ 3 (+ 4 5)))))
                (set 15))
  (check-equal? (car (-->>PCF₃ '(<= 1 2))) (set #t))
  (check-equal? (car (-->>PCF₃ '(<= 3 2))) (set #f))
  (check-equal? (-->PCF₃ '(if #f 3 2)) (set 2))
  (check-equal? (-->PCF₃ '(if #t 3 2)) (set 3))
  (check-equal? (-->PCF₃ '(if 8 3 2)) (set 3))
  (check-equal? (-->PCF₃ '(if (<= 10 8) 3 2)) (set '(if #f 3 2)))
  (check-equal? (car (-->>PCF₃ '(if #f 3 2))) (set 2))
  (check-equal? (car (-->>PCF₃ '(if #t 3 2))) (set 3))
  (check-equal? (car (-->>PCF₃ '(if 8 3 2))) (set 3))
  (check-equal? (car (-->>PCF₃ '(if (<= 10 8) 3 2))) (set 2))
  (check-equal? (car (-->>PCF₃ '(if (+ 10 8) 3 2))) (set 3))
  (check-equal? (car (-->>PCF₃ '(if (<= 10 108) 3 2)))
                (set 3))
  (check-equal?
   (car (-->>PCF₃ '(if (if (<= 10 108) #f #t)
                     (+ (+ 1 2) 3)
                     (+ (+ 1 2) (+ 3 (+ 4 5))))))
   (set 15))
  (check-equal?
   (car (-->>PCF₃ '(((if (if (<= 10 108) #f #t)
                       (λ (x) (λ (y) x))
                       (λ (x) (λ (y) y))) 1) 2)))
   (set 2))
  ;; ↓substをオーバーライドしてないから動かない！
  #;
  (car (-->>PCF₃ '(((if (if (<= 108 10) #f #t)
                      (λ (x) (λ (y) x))
                      (λ (x) (λ (y) y))) 1) 2)))
  #;
  (check-equal?
   (car (-->>PCF₃ '(fix ((λ (x) x) (λ (y) y)))))
   (set '(λ (y1892504) ((fix (λ (y) y)) y1892504))))
  )

;; ... とここまでして，実は subst は親の定義のままではダメ！
;; さらなる目標としては，call-by-name (もしくはnondetなfull-reduction)に
;; するのに，EC だけオーバーライドして実現したい！
;;  なんらかの方法で上手くオーバーライドする方法がないと．．．で次節につづく

(module+ test
  ;(printf "----- PCF₃ part2 ------------\n")
  (check-equal? (car (-->>PCF₃ '((λ (x) x) 2))) (set 2)) ; OK
  ;(-->>PCF₃ '((λ (x) 1) 2))
  ;(-->>PCF₃ '((λ (x) #t) 2))
  ;(-->>PCF₃ '((λ (x) (+ x 1)) 2))
  ;(-->>PCF₃ '((λ (x) (<= 1 x)) 2))
  ;(-->>PCF₃ '((λ (x) (if x x 0)) 2))
  #;
  (check-equal?
   (car (-->>PCF₃ '((λ (x) (fix x)) (λ (y) y))))
   (set '(λ (y1947664) ((fix (λ (y) y)) y1947664)))) ; appと誤認識
  )

;;;; 「レキシカルスコープからの逸脱」機能説明のためのコード
;;;; design2.rktで継承

(define (f x) `(+ ,x 1))

(define-reduction (-->₂-rule)
  [`(f ,x) (f x) "f"])

(module+ test
  ;(printf "----- -->₂ ------------\n")
  (define-values (mrun₂ reducer₂) (-->₂-rule))
  (define -->₂ (compose1 mrun₂ reducer₂))
  (check-equal? (-->₂ '(f a)) (set '(+ a 1))))

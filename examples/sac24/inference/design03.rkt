#lang racket
(require lightstep/base lightstep/syntax lightstep/inference
         (for-syntax syntax/parse syntax/stx)
         (only-in "design02.rkt" subst)
         (only-in "design02.rkt" PCF₀ -->PCF₀-rules))
(provide PCF₂ -->PCF₃-rule -->₂-rule E)

(module+ test (require rackunit))

;; 自分自身を埋め込めることで，evaluation-contextの再帰構造をシンプルに表現できる
;;   if-trueのオーバーライド (Vの追加)

(define-language PCF₂ #:super PCF₀
  [V ∷= #t #f N  `(λ (,X) ,M)])

(define-inference (-->PCF₂-rules) #:super [(-->PCF₀-rules)]
  ;; override
  [M′ ≔ (subst M X V)
   ------------------------- "β"
   `(((λ (,X) ,M) ,V) → ,M′)]

  ;; override
  [#:when (not (false? V₁))
   ------------------------- "if-true"
   `((if ,V₁ ,M₂ ,M₃) → ,M₂)]

  [`(,M₁ → ,M₁′)
   ------------------------- "EC-app1"
   `((,M₁ ,M₂) → (,M₁′ ,M₂))]

  [`(,M → ,M′)
   --------------------- "EC-app2"
   `((,V ,M) → (,V ,M′))]

  [`(,M₁ → ,M₁′)
   ----------------------------- "EC-add1"
   `((+ ,M₁ ,M₂) → (+ ,M₁′ ,M₂))]

  [`(,M → ,M′)
   ------------------------- "EC-add2"
   `((+ ,V ,M) → (+ ,V ,M′))]

  [`(,M₁ → ,M₁′)
   ------------------------------- "EC-le1"
   `((<= ,M₁ ,M₂) → (<= ,M₁′ ,M₂))]

  [`(,M → ,M′)
   --------------------------- "EC-le2"
   `((<= ,V ,M) → (<= ,V ,M′))]

  [`(,M₁ → ,M₁′)
   --------------------------------------- "EC-if"
   `((if ,M₁ ,M₂ ,M₃) → (if ,M₁′ ,M₂ ,M₃))]

  [`(,M → ,M′)
   ----------------------- "EC-fix"
   `((fix ,M) → (fix ,M′))])

(define -->PCF₂ (call-with-values (λ () (-->PCF₂-rules)) compose1))
(define -->>PCF₂ (compose1 car (repeated -->PCF₂)))

(module+ test
  ;(printf "----- PCF₂ ------------\n")
  (check-equal? (-->>PCF₂ '(+ 1 2)) (set 3))
  (check-equal? (-->>PCF₂ '(+ (+ 1 2) 3)) (set 6))
  (check-equal? (-->>PCF₂ '(+ (+ 1 2) (+ 3 (+ 4 5))))
                (set 15))
  (check-equal? (-->>PCF₂ '(<= 1 2)) (set #t))
  (check-equal? (-->>PCF₂ '(<= 3 2)) (set #f))
  (check-equal? (-->PCF₂ '(if #f 3 2)) (set 2))
  (check-equal? (-->PCF₂ '(if #t 3 2)) (set 3))
  (check-equal? (-->PCF₂ '(if 8 3 2)) (set 3))
  (check-equal? (-->PCF₂ '(if (<= 10 8) 3 2)) (set '(if #f 3 2)))
  (check-equal? (-->>PCF₂ '(if #f 3 2)) (set 2))
  (check-equal? (-->>PCF₂ '(if #t 3 2)) (set 3))
  (check-equal? (-->>PCF₂ '(if 8 3 2)) (set 3))
  (check-equal? (-->>PCF₂ '(if (<= 10 8) 3 2)) (set 2))
  (check-equal? (-->>PCF₂ '(if (+ 10 8) 3 2)) (set 3))
  (check-equal? (-->>PCF₂ '(if (<= 10 108) 3 2))
                (set 3))
  (check-equal?
   (-->>PCF₂ '(if (if (<= 10 108) #f #t)
                (+ (+ 1 2) 3)
                (+ (+ 1 2) (+ 3 (+ 4 5)))))
   (set 15))
  (check-equal?
   (-->>PCF₂ '(((if (if (<= 10 108) #f #t)
                  (λ (x) (λ (y) x))
                  (λ (x) (λ (y) y))) 1) 2))
   (set 2))
  ;; ↓substをオーバーライドしてないから動かない！
  #;
  (-->>PCF₂ '(((if (if (<= 108 10) #f #t)
                 (λ (x) (λ (y) x))
                 (λ (x) (λ (y) y))) 1) 2))
  #;
  (check-equal?
   (-->>PCF₂ '(fix ((λ (x) x) (λ (y) y))))
   (set '(λ (y1701765) ((fix (λ (y) y)) y1701765))))
  )

;; 各ルール中に遷移を埋め込むかわりに，cxtマッチエクスパンダを定義すれば
;; モジュール化．後の subreduction オーバーライドの対象にもできる．
;; 以下，SAC'24時点とは異なる改良版の cxt を用いることにする．

;; この定義は載せる
(define-match-expander E
  (syntax-parser
    [(E p)
     #'(cxt E [□ (and p (or `((λ (,(? X?)) ,_) ,(? V?))
                            `(+ ,(? N?) ,(? N?))
                            `(<= ,(? N?) ,(? N?))
                            `(if ,(? V?) ,_ ,_)
                            `(fix (λ (,(? X?)) ,_))))]
            `(+ ,V ,□)
            `(+ ,□ ,M)
            `(<= ,V ,□)
            `(<= ,□ ,M)
            `(if ,□ ,M₁ ,M₂)
            `(fix ,□)
            `(,V ,□)
            `(,□ ,M₁))]))

(module+ test
  ;(printf "----- EC ------------\n")
  (check-equal?
   (match '(if (+ 1 2) (+ 3 4) 5)
     [(E e) (E `(<= ,e ,e))])
   '(if (<= (+ 1 2) (+ 1 2)) (+ 3 4) 5)))


(define-inference (-->PCF₃-rule)
  #:do [(define-inference (-->PCF₀′-rules) #:super [(-->PCF₀-rules)]
          ;; override
          [------------------------------------ "β"
           `(((λ (,X) ,M) ,V) → ,(subst M X V))]

          ;; override
          [#:when (not (false? V₁))
           ------------------------- "if-true"
           `((if ,V₁ ,M₂ ,M₃) → ,M₂)])
        (define →PCF₀′ (reducer-of (-->PCF₀′-rules)))]
  #:forms (.... [`(,i →₀ ,o) #:where o ← (→PCF₀′ i)])

  [`(,M →₀ ,M′)
   ----------------- "EC"
   `(,(E M) → ,(E M′))])

(define -->PCF₃ (call-with-values (λ () (-->PCF₃-rule)) compose1))
(define -->>PCF₃ (compose1 car (repeated -->PCF₃)))

(module+ test
  ;(printf "----- PCF₃ ------------\n")
  (check-equal? (-->>PCF₃ '(+ 1 2)) (set 3))
  (check-equal? (-->>PCF₃ '(+ (+ 1 2) 3)) (set 6))
  (check-equal? (-->>PCF₃ '(+ (+ 1 2) (+ 3 (+ 4 5))))
                (set 15))
  (check-equal? (-->>PCF₃ '(<= 1 2)) (set #t))
  (check-equal? (-->>PCF₃ '(<= 3 2)) (set #f))
  (check-equal? (-->PCF₃ '(if #f 3 2)) (set 2))
  (check-equal? (-->PCF₃ '(if #t 3 2)) (set 3))
  (check-equal? (-->PCF₃ '(if 8 3 2)) (set 3))
  (check-equal? (-->PCF₃ '(if (<= 10 8) 3 2)) (set '(if #f 3 2)))
  (check-equal? (-->>PCF₃ '(if #f 3 2)) (set 2))
  (check-equal? (-->>PCF₃ '(if #t 3 2)) (set 3))
  (check-equal? (-->>PCF₃ '(if 8 3 2)) (set 3))
  (check-equal? (-->>PCF₃ '(if (<= 10 8) 3 2)) (set 2))
  (check-equal? (-->>PCF₃ '(if (+ 10 8) 3 2)) (set 3))
  (check-equal? (-->>PCF₃ '(if (<= 10 108) 3 2))
                (set 3))
  (check-equal?
   (-->>PCF₃ '(if (if (<= 10 108) #f #t)
                (+ (+ 1 2) 3)
                (+ (+ 1 2) (+ 3 (+ 4 5)))))
   (set 15))
  (check-equal?
   (-->>PCF₃ '(((if (if (<= 10 108) #f #t)
                  (λ (x) (λ (y) x))
                  (λ (x) (λ (y) y))) 1) 2))
   (set 2))

  ;; ↓substをオーバーライドしてないから動かない！
  #;
  (-->>PCF₃ '(((if (if (<= 108 10) #f #t)
                 (λ (x) (λ (y) x))
                 (λ (x) (λ (y) y))) 1) 2))
  #;
  (check-equal?
   (-->>PCF₃ '(fix ((λ (x) x) (λ (y) y))))
   (set '(λ (y1892504) ((fix (λ (y) y)) y1892504))))
  )

;; ... とここまでして，実は subst は親の定義のままではダメ！
;; さらなる目標としては，call-by-name (もしくはnondetなfull-reduction)に
;; するのに，EC だけオーバーライドして実現したい！
;;  なんらかの方法で上手くオーバーライドする方法がないと．．．で次節につづく

(module+ test
  ;(printf "----- PCF₃ part2 ------------\n")
  (check-equal? (-->>PCF₃ '((λ (x) x) 2)) (set 2)) ; OK
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
;;;; design04.rktで継承

(define (f x) `(+ ,x 1))

(define-inference (-->₂-rule)
  [------------------ "f"
   `((f ,x) → ,(f x))])
(define -->₂ (call-with-values (λ () (-->₂-rule)) compose1))

(module+ test
  ;(printf "----- -->₂ ------------\n")
  (check-equal? (-->₂ '(f a)) (set '(+ a 1))))

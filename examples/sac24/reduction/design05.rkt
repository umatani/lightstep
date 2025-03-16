#lang racket
(require (for-syntax syntax/parse)
         lightstep/base lightstep/syntax
         (only-in racket/random random-ref)
         (only-in "design03.rkt" PCF₂)
         (only-in "design04.rkt" [subst orig:subst]))
(provide PCF₅ subst E -->PCF₅)

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
;;  (b) ≔<1>, ≔<2> をパラメータ化
;;      SAC24時点では EC規則 の継承が可能なよう，自己参照もパラメータ --> による
;;      open recursion を用いていたが，lightstepではルール名で直接自分自身の
;;      reducerを参照可能なように改良してある．

(define-language PCF₅ #:super PCF₂
  [M ∷= .... `(amb ,M ...)]
  [KWD ∷= .... 'amb])

(define/match (subst n x m) #:super orig:subst
  [(`(amb ,M ...) X M)
   `(amb ,@(map (λ (e) (subst e X M)) M))])

(define-match-expander E
  (syntax-parser
    [(E p)
     #'(cxt E [□ (and p (or `((λ (,(? X?)) ,_) ,(? V?))
                            `(+ ,(? N?) ,(? N?))
                            `(<= ,(? N?) ,(? N?))
                            `(if ,(? V?) ,_ ,_)
                            `(fix (λ (,(? X?)) ,_))
                            `(amb ,(? M?) (... ...)) ;; NEW
                            ))]
            `(+ ,V ,□)
            `(+ ,□ ,M)
            `(<= ,V ,□)
            `(<= ,□ ,M)
            `(if ,□ ,M₁ ,M₂)
            `(fix ,□)
            `(,V ,□)
            `(,□ ,M₁))]))

(define (select es)
  (random-ref es))

(define-reduction (-->PCF₅ ≔<1> ≔<2>)
  #:do [(define-reduction (PCF₅)
          [`((λ (,X) ,M) ,V) (subst M X V) "β"]
          [`(+ ,N₁ ,N₂) (+ N₁ N₂) "add"]
          [`(<= ,N₁ ,N₂)
           M ≔<1> (<= N₁ N₂)
           M "le"]
          [`(if #f ,M₂ ,M₃) M₃ "if-false"]
          [`(if ,V₁ ,M₂ ,M₃)
           #:when (not (false? V₁))
           M₂ "if-true"]
          [`(fix (λ (,X) ,M))
           X′ ≔<1> (gensym X)
           `((λ (,X) ,M) (λ (,X′) ((fix (λ (,X) ,M)) ,X′)))
           "fix"]
          [`(amb ,M ...)
           M′ ≔<2> (select M)
           M′
           "amb"])
        (define →PCF₅ (reducer-of (PCF₅)))]
  [(E M)
   M′ ← (→PCF₅ M)
   (E M′)
   "EC"])

;; One benefit of parameterization over non-lexical extension is ...
(define step-->PCF₅ (call-with-values (λ () (-->PCF₅ ≔ ≔)) compose1))
(define -->>PCF₅ (compose1 car (repeated step-->PCF₅)))

(module+ test
  ;(printf "----- PCF₅ ------------\n")
  (check-not-exn (λ () (-->>PCF₅ '(amb 1 2 3 4 5))))
  (check-not-exn (λ () (-->>PCF₅ '(+ (amb 1 2 3 4) (amb 10 20 30 40))))))

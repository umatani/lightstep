#lang racket
(require (for-syntax syntax/parse)
         lightstep/base lightstep/syntax lightstep/inference
         (only-in "design03.rkt" PCF₂))

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

;; SAC24との相違．misc^ を syntax^ に．
;; 言語ではなく，必要最低限の述語だけをexport

(define-signature syntax^
  (M? X? V? N? subst))

(define-unit syntax1@
  (import)
  (export syntax^)

  ;; 言語定義のインポート
  (define-language PCF₇ #:super PCF₂)

  ;; as before
  (define/match (subst-m n x m)
    [(N X M) N]
    [((? boolean? b) X M) b]
    [(`(+ ,M₁ ,M₂) X M)
     `(+ ,(subst-m M₁ X M) ,(subst-m M₂ X M))]
    [(`(<= ,M₁ ,M₂) X M)
     `(<= ,(subst-m M₁ X M) ,(subst-m M₂ X M))]
    [(`(if ,M₁ ,M₂ ,M₃) X M)
     `(if ,(subst-m M₁ X M) ,(subst-m M₂ X M) ,(subst-m M₃ X M))]
    [(`(fix ,M′) X M)
     `(fix ,(subst-m M′ X M))]
    [(X′ X M)
     (if (eq? X X′) M X′)]
    [(`(λ (,X′) ,M′) X M)
     (if (eq? X X′)
       `(λ (,X′) ,M′)
       (let ([X″ (gensym X′)])
         `(λ (,X″) ,(subst-m (subst-m M′ X′ X″) X M))))]
    [(`(,M₁ ,M₂) X M) `(,(subst-m M₁ X M) ,(subst-m M₂ X M))])

  (define (subst n x m) (subst-m n x m)))

(define-inference (-->PCF₇)
  #:import (delta^ syntax^)
  #:do [;; as before
        (define-match-expander E
          (syntax-parser
            [(E □)
             #'(cxt E [□ (and □ (or `((λ (,(? X?)) ,_) ,(? V?))
                                    `(,(? prim?) ,(? V?) (... ...))
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
        (define-inference (PCF₇)
          [------------------------------------- "prim"
           `((,(? prim? op) ,V ...) → ,(δ op V))]

          [------------------------------------ "β"
           `(((λ (,X) ,M) ,V) → ,(subst M X V))]

          [------------------------ "if-false"
           `((if #f ,M₂ ,M₃) → ,M₃)]

          [#:when (not (false? V₁))
           ------------------------- "if-true"
           `((if ,V₁ ,M₂ ,M₃) → ,M₂)]

          [X′ ≔ (gensym X)
           ---------------------------------------- "fix"
           `((fix (λ (,X) ,M))
             → ((λ (,X) ,M)
                (λ (,X′) ((fix (λ (,X) ,M)) ,X′))))])

        (define →PCF₇ (reducer-of (PCF₇)))]
  #:forms (.... [`(,i →₇ ,o) #:where o ← (→PCF₇ i)])

  [`(,m →₇ ,M′)
   ------------------- "EC"
   `(,(E m) → ,(E M′))])

(define step-->PCF₇
  (call-with-values
   (λ () (invoke-unit
          (compound-unit (import) (export)
                         (link (([s : syntax^]) syntax1@)
                               (([d : delta^]) delta1@)
                               (() (-->PCF₇) s d)))))
   compose1))
(define -->>PCF₇ (compose1 car (repeated step-->PCF₇)))

(module+ test
  ;(printf "----- PCF₇ ------------\n")
  (check-equal? (-->>PCF₇ '(+ 1 2)) (set 3))
  (check-equal? (-->>PCF₇ '(+ (+ 1 2) 3)) (set 6))
  (check-equal? (-->>PCF₇ '(+ (+ 1 2) (+ 3 (+ 7 5))))
                (set 18))
  (check-equal? (-->>PCF₇ '(<= 1 2)) (set #t))
  (check-equal? (-->>PCF₇ '(<= 3 2)) (set #f))
  (check-equal? (-->>PCF₇ '(if #f 3 2)) (set 2))
  (check-equal? (-->>PCF₇ '(if #t 3 2)) (set 3))
  (check-equal? (-->>PCF₇ '(if 8 3 2)) (set 3))
  (check-equal? (-->>PCF₇ '(if (<= 10 8) 3 2)) (set 2))
  (check-equal? (-->>PCF₇ '(if (+ 10 8) 3 2)) (set 3))
  (check-equal? (-->>PCF₇ '(if (<= 10 108) 3 2))
                (set 3))
  (check-equal?
   (-->>PCF₇ '(if (if (<= 10 108) #f #t)
                (+ (+ 1 2) 3)
                (+ (+ 1 2) (+ 3 (+ 7 5)))))
   (set 18))
  (check-equal?
   (-->>PCF₇ '(((if (if (<= 10 108) #f #t)
                  (λ (x) (λ (y) x))
                  (λ (x) (λ (y) y))) 1) 2))
   (set 2))
  (check-equal?
   (-->>PCF₇ '(((if (if (<= 108 10) #f #t)
                  (λ (x) (λ (y) x))
                  (λ (x) (λ (y) y))) 1) 2))
   (set 1))
  #;
  (check-equal?
   (-->>PCF₇ '(fix ((λ (x) x) (λ (y) y))))
   (set '(λ (y2845333) ((fix (λ (y) y)) y2845333))))
  (check-equal? (-->>PCF₇ '((λ (x) x) 2)) (set 2))
  (check-equal? (-->>PCF₇ '((λ (x) 1) 2)) (set 1))
  (check-equal? (-->>PCF₇ '((λ (x) #t) 2)) (set #t))
  (check-equal? (-->>PCF₇ '((λ (x) (+ x 1)) 2))
                (set 3))
  (check-equal? (-->>PCF₇ '((λ (x) (<= 1 x)) 2))
                (set #t))
  (check-equal? (-->>PCF₇ '((λ (x) (if x x 0)) 2))
                (set 2))
  #;
  (check-equal? (-->>PCF₇ '((λ (x) (fix x)) (λ (y) y)))
                (set '(λ (y2904847) ((fix (λ (y) y)) y2904847)))))

;; (2) eval関数 in δ

(define-unit delta2@
  (import red^)
  (export delta^)

  (define (prim? op)
    (member op '(+ <= eval)))

  (define -->> (compose1 car (repeated (compose1 mrun reducer))))

  (define (δ op vs)
    (case op
      [(eval)
       (match (-->> (cadar vs))
         [(set v) v])]
      ; as before
      [(+)  (apply + vs)]
      [(<=) (apply <= vs)]))
  
  (values mrun reducer))

(define-unit syntax2@
  (import)
  (export syntax^)

  (define-language PCF₈ #:super PCF₂
    [M ∷= .... `(quote ,M)]
    [V ∷= .... `(quote ,M)]
    [KWD ∷= .... 'quote])

  ;; as before
  (define/match (subst-m n x m)
    [(`(quote ,M′) X M) `(quote ,M′)] ;; NEW
    [(N X M) N]
    [((? boolean? b) X M) b]
    [(`(+ ,M₁ ,M₂) X M)
     `(+ ,(subst-m M₁ X M) ,(subst-m M₂ X M))]
    [(`(<= ,M₁ ,M₂) X M)
     `(<= ,(subst-m M₁ X M) ,(subst-m M₂ X M))]
    [(`(if ,M₁ ,M₂ ,M₃) X M)
     `(if ,(subst-m M₁ X M) ,(subst-m M₂ X M) ,(subst-m M₃ X M))]
    [(`(fix ,M′) X M)
     `(fix ,(subst-m M′ X M))]
    [(X′ X M)
     (if (eq? X X′) M X′)]
    [(`(λ (,X′) ,M′) X M)
     (if (eq? X X′)
       `(λ (,X′) ,M′)
       (let ([X″ (gensym X′)])
         `(λ (,X″) ,(subst-m (subst-m M′ X′ X″) X M))))]
    [(`(,M₁ ,M₂) X M) `(,(subst-m M₁ X M) ,(subst-m M₂ X M))])

  (define (subst n x m) (subst-m n x m)))

(define-inference (-->PCF₈) #:super [(-->PCF₇)])

(define step-->PCF₈
  (call-with-values
   (λ () (invoke-unit
          (compound-unit (import) (export)
                         (link (([s : syntax^]) syntax2@)
                               (([r : red^]) (-->PCF₈) s d)
                               (([d : delta^]) delta2@ r)))))
   compose1))
(define -->>PCF₈ (compose1 car (repeated step-->PCF₈)))

(module+ test
  ;;(printf "----- PCF₈ ------------\n")
  (check-equal? (step-->PCF₈ '(eval '(+ 1 2))) (set 3))
  (check-equal?
   (-->>PCF₈ '(+ (eval '(+ 1 2)) (eval '(+ (+ 3 (+ 4 5)) (+ 1 2)))))
   (set 18)))

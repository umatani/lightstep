#lang racket
(require lightstep/base lightstep/syntax lightstep/inference
         (only-in "design01.rkt" [subst LAM:subst])
         (only-in "design02.rkt" -->PCF₀)
         (only-in "design03.rkt" PCF₂ E -->₂ -->PCF₃))
(provide subst)

(module+ test (require rackunit))

;;;;;;;;;; 拡張性のためのさらなる機能
;;;; ここまで見てきたとおり，#:super で rule 単位のオーバーライドができれば
;;;; かなりのことは書けるが．．．
;;;; ★ (1) レキシカルスコープからの逸脱．実用例は？ これが一つの目玉
;;;;      従来の Redex では不可能な最も重要な LWRedex の機能は，．．．
;;;;      subst, EC等々，まわりの補助定義がたくさん増えていく

;; まずは無意味な例で機能説明

(define (f x) `(+ ,x ,x))
(define (g x) `(<= 0 ,x))

;; ちなみに，下の簡潔な例で，Redexとは異なり，quasiquote, unquote
;; を明示的に書くRacketのパターンの美しさが際立つ．
;; xは常にメタ変数を意味することや，gは両方の世界にありそれぞれどちらに属するかが一目瞭然．
(define-inference (-->₃) #:super [(-->₂)]
  [------------------ "g"
   `((g ,x) → ,(g x))])

(module+ test
  ;(printf "----- -->₃ ------------\n")
  (define step-->₃ (call-with-values (λ () (-->₃)) compose1))
  (check-equal? (step-->₃ '(g a)) (set '(<= 0 a))) ;; as usual
  (check-equal? (step-->₃ '(f a)) (set '(+ a a))))

;; 言語定義のインポート
(define-language PCF₄ #:super PCF₂)

;; substのオーバーライド
(define/match (subst n x m) #:super LAM:subst
  [(N X M) N]
  [((? boolean? b) X M) b]
  [(`(+ ,M₁ ,M₂) X M)
   `(+ ,(subst M₁ X M) ,(subst M₂ X M))]
  [(`(<= ,M₁ ,M₂) X M)
   `(<= ,(subst M₁ X M) ,(subst M₂ X M))]
  [(`(if ,M₁ ,M₂ ,M₃) X M)
   `(if ,(subst M₁ X M) ,(subst M₂ X M) ,(subst M₃ X M))]
  [(`(fix ,M′) X M)
   `(fix ,(subst M′ X M))])

(define-inference (-->PCF₄) #:super [(-->PCF₃)])
(define step-->PCF₄ (call-with-values (λ () (-->PCF₄)) compose1))
(define -->>PCF₄ (compose1 car (repeated step-->PCF₄)))

(module+ test
  ;(printf "----- PCF₄ ------------\n")
  (check-equal? (-->>PCF₄ '(+ 1 2)) (set 3))
  (check-equal? (-->>PCF₄ '(+ (+ 1 2) 3)) (set 6))
  (check-equal? (-->>PCF₄ '(+ (+ 1 2) (+ 3 (+ 4 5))))
                (set 15))
  (check-equal? (-->>PCF₄ '(<= 1 2)) (set #t))
  (check-equal? (-->>PCF₄ '(<= 3 2)) (set #f))
  (check-equal? (-->>PCF₄ '(if #f 3 2)) (set 2))
  (check-equal? (-->>PCF₄ '(if #t 3 2)) (set 3))
  (check-equal? (-->>PCF₄ '(if 8 3 2)) (set 3))
  (check-equal? (-->>PCF₄ '(if (<= 10 8) 3 2)) (set 2))
  (check-equal? (-->>PCF₄ '(if (+ 10 8) 3 2)) (set 3))
  (check-equal? (-->>PCF₄ '(if (<= 10 108) 3 2))
                (set 3))
  (check-equal?
   (-->>PCF₄ '(if (if (<= 10 108) #f #t)
                     (+ (+ 1 2) 3)
                     (+ (+ 1 2) (+ 3 (+ 4 5)))))
   (set 15))
  (check-equal?
   (-->>PCF₄ '(((if (if (<= 10 108) #f #t)
                       (λ (x) (λ (y) x))
                       (λ (x) (λ (y) y))) 1) 2))
   (set 2))
  (check-equal?
   (-->>PCF₄ '(((if (if (<= 108 10) #f #t)
                       (λ (x) (λ (y) x))
                       (λ (x) (λ (y) y))) 1) 2))
   (set 1))
  #;
  (check-equal?
   (-->>PCF₄ '(fix ((λ (x) x) (λ (y) y))))
   (set '(λ (y2295546) ((fix (λ (y) y)) y2295546))))
  (check-equal? (-->>PCF₄ '((λ (x) x) 2)) (set 2))
  (check-equal? (-->>PCF₄ '((λ (x) 1) 2)) (set 1))
  (check-equal? (-->>PCF₄ '((λ (x) #t) 2)) (set #t))
  (check-equal? (-->>PCF₄ '((λ (x) (+ x 1)) 2))
                (set 3))
  (check-equal? (-->>PCF₄ '((λ (x) (<= 1 x)) 2))
                (set #t))
  (check-equal? (-->>PCF₄ '((λ (x) (if x x 0)) 2))
                (set 2))
  #;
  (check-equal?
   (-->>PCF₄ '((λ (x) (fix x)) (λ (y) y)))
   (set '(λ (y2318202) ((fix (λ (y) y)) y2318202)))))

#lang racket
(require lightstep/base
         (only-in "design1.rkt" val? ECxt -->₂-rule -->PCF₃-rule))
(provide -->PCF₄-rule subst)

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

(define-reduction (-->₃-rule) #:super (-->₂-rule)
  [`(g ,x) (g x) "g"])

(module+ test
  ;(printf "----- -->₃ ------------\n")
  (define -->₃ (call-with-values
                (λ () (invoke-unit (-->₃-rule)))
                (λ (mrun reducer) (compose1 mrun reducer))))
  (check-equal? (-->₃ '(g a)) (set '(<= 0 a))) ;; as usual
  (check-equal? (-->₃ '(f a)) (set '(+ a a))))

;; substのオーバーライド
(define (subst e x e′)
  (match e
    [(? number? n) n]
    [(? boolean? b) b]
    [`(+ ,e₁ ,e₂) `(+ ,(subst e₁ x e′) ,(subst e₂ x e′))]
    [`(<= ,e₁ ,e₂) `(<= ,(subst e₁ x e′) ,(subst e₂ x e′))]
    [`(if ,e₁ ,e₂ ,e3) `(if ,(subst e₁ x e′) ,(subst e₂ x e′) ,(subst e3 x e′))]
    [`(fix ,e) `(fix ,(subst e x e′))]

    [(? symbol? y) (if (eq? x y) e′ e)]
    [`(λ (,(? symbol? y)) ,e₁)
     (if (eq? x y)
         `(λ (,y) ,e₁)
         (let ([y-new (gensym y)])
           `(λ (,y-new) ,(subst (subst e₁ y y-new) x e′))))]
    [`(,e₁ ,e₂) `(,(subst e₁ x e′) ,(subst e₂ x e′))]
    ;[_ (subst0 e x e′)] ;; これはダメ
    ))

(define-reduction (-->PCF₄-rule) #:super (-->PCF₃-rule)
  [(ECxt e)
   e′ ← (-->PCF₄ e) ;; override (PCF₃ -> PCF₄)
   (ECxt e′)
   "EC"])
(define -->PCF₄ (call-with-values
                 (λ () (invoke-unit (-->PCF₄-rule)))
                 (λ (mrun reducer) (compose1 mrun reducer))))
(define -->>PCF₄ (repeated -->PCF₄))

(module+ test
  ;(printf "----- PCF₄ ------------\n")
  (check-equal? (car (-->>PCF₄ '(+ 1 2))) (set 3))
  (check-equal? (car (-->>PCF₄ '(+ (+ 1 2) 3))) (set 6))
  (check-equal? (car (-->>PCF₄ '(+ (+ 1 2) (+ 3 (+ 4 5)))))
                (set 15))
  (check-equal? (car (-->>PCF₄ '(<= 1 2))) (set #t))
  (check-equal? (car (-->>PCF₄ '(<= 3 2))) (set #f))
  (check-equal? (car (-->>PCF₄ '(if #f 3 2))) (set 2))
  (check-equal? (car (-->>PCF₄ '(if #t 3 2))) (set 3))
  (check-equal? (car (-->>PCF₄ '(if 8 3 2))) (set 3))
  (check-equal? (car (-->>PCF₄ '(if (<= 10 8) 3 2))) (set 2))
  (check-equal? (car (-->>PCF₄ '(if (+ 10 8) 3 2))) (set 3))
  (check-equal? (car (-->>PCF₄ '(if (<= 10 108) 3 2)))
                (set 3))
  (check-equal?
   (car (-->>PCF₄ '(if (if (<= 10 108) #f #t)
                     (+ (+ 1 2) 3)
                     (+ (+ 1 2) (+ 3 (+ 4 5))))))
   (set 15))
  (check-equal?
   (car (-->>PCF₄ '(((if (if (<= 10 108) #f #t)
                       (λ (x) (λ (y) x))
                       (λ (x) (λ (y) y))) 1) 2)))
   (set 2))
  (check-equal?
   (car (-->>PCF₄ '(((if (if (<= 108 10) #f #t)
                       (λ (x) (λ (y) x))
                       (λ (x) (λ (y) y))) 1) 2)))
   (set 1))
  #;
  (check-equal?
   (car (-->>PCF₄ '(fix ((λ (x) x) (λ (y) y)))))
   (set '(λ (y2295546) ((fix (λ (y) y)) y2295546))))
  (check-equal? (car (-->>PCF₄ '((λ (x) x) 2))) (set 2))
  (check-equal? (car (-->>PCF₄ '((λ (x) 1) 2))) (set 1))
  (check-equal? (car (-->>PCF₄ '((λ (x) #t) 2))) (set #t))
  (check-equal? (car (-->>PCF₄ '((λ (x) (+ x 1)) 2)))
                (set 3))
  (check-equal? (car (-->>PCF₄ '((λ (x) (<= 1 x)) 2)))
                (set #t))
  (check-equal? (car (-->>PCF₄ '((λ (x) (if x x 0)) 2)))
                (set 2))
  #;
  (check-equal?
   (car (-->>PCF₄ '((λ (x) (fix x)) (λ (y) y))))
   (set '(λ (y2318202) ((fix (λ (y) y)) y2318202)))))

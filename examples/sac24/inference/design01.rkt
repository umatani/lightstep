#lang racket
(require lightstep/base lightstep/syntax lightstep/inference)
(provide LAM subst -->LAM)

(module+ test (require rackunit))

;;;;;; define-inferenceバージョン
;; Redexと異なり，reductionとinferenceで書かるものが異なる．
;; lightstepでは，small-step, big-step, type system 等，
;; すべてを両方で書ける．両者の違いは単に表面的な見た目だけ．


;;;;;;;;;; 基本機能

;; rule setの書き方の基本
;;   Racket 標準の match の pattern をそのまま利用可能
(define-inference (-->₀)
  [------------------- "car"
   `(,(cons x y) → ,x)])

;; parameterized rule set のため (引数ありは後述2)
(define-values (mrun₀ reducer₀) (-->₀))
(define step-->₀ (compose1 mrun₀ reducer₀))

(module+ test
  ;(printf "---- cons -------------\n")
  ;; reducer とは (-> state (Setof state))
  (check-equal? (step-->₀ (cons 1 2)) (set 1))

  ;; (repeated step-->) は multi-step
  ;;   set of irreducible term を返す
  ;;   irreducible = どのルールにもマッチしなかった state
  (check-equal? (step-->₀ (cons (cons 1 2) 3)) (set '(1 . 2)))

  (check-equal?
   (car ((repeated step-->₀) (cons (cons 1 2) 3)))
   (set 1)))

;; 非決定的である例
(define-inference (-->₁)
  [------------------- "car"
   `((,x . ,y) → ,x)]

  [------------------- "cdr"
   `((,x . ,y) → ,y)])

(define step-->₁ (call-with-values (λ () (-->₁)) compose1))

(module+ test
  (check-equal? (step-->₁ (cons (cons 1 2) 3)) (set 3 '(1 . 2)))

  (check-equal? (car ((repeated step-->₁) (cons (cons 1 2) 3)))
                (set 1 2 3)))

;; 例：ここまでの機能で untyped pure λ-calculus の β

(define-language LAM
  [M ∷= X `(λ (,X) ,M) `(,M₁ ,M₂)]
  [X ∷= (and (? symbol?) (? (λ (x) (not (KWD? x)))))]
  [KWD ∷= 'λ])

; subst : M X M -> M
(define/match (subst n x m)
  [(X′ X M)
   (if (eq? X X′) M X′)]
  [(`(λ (,X′) ,M′) X M)
   (if (eq? X X′)
     `(λ (,X′) ,M′)
     (let ([X″ (gensym X′)])
       `(λ (,X″) ,(subst (subst M′ X′ X″) X M))))]
  [(`(,M₁ ,M₂) X M) `(,(subst M₁ X M) ,(subst M₂ X M))])

(define-inference (-->LAM)
  [--------------------- "β"
   `(((λ (,X) ,M₁) ,M₂)
     → ,(subst M₁ X M₂))])

(define step-->LAM (call-with-values (λ () (-->LAM)) compose1))
(define -->>LAM (compose car (repeated step-->LAM)))

(module+ test
  ;(printf "---- LAM -------------\n")
  ;; 下と一緒
  ;; (-->LAM '((λ (x) x) (λ (z) (z z))))
  ;; (-->LAM '((λ (x) (λ (z) (x z))) (λ (z) (x z))))
  (check-equal?
   (-->>LAM '((λ (x) x) (λ (z) (z z))))
   (set '(λ (z) (z z))))

  #;
  (check-equal?
   (-->>LAM '((λ (x) (λ (z) (x z))) (λ (z) (x z))))
   (set '(λ (z685121) ((λ (z) (x z)) z685121))))

  (check-equal?
   (step-->LAM '((λ (x) (x x)) (λ (z) (z z))))
   (set '((λ (z) (z z)) (λ (z) (z z)))))
  ;; cycleもちゃんと検出
  (check-equal? (-->>LAM '((λ (x) (x x)) (λ (z) (z z))))
                (set)))

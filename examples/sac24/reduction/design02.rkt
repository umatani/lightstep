#lang racket
(require lightstep/base lightstep/syntax
         (only-in "design01.rkt" LAM [subst LAM:subst] -->LAM))
(provide PCF₀ subst -->PCF₀)

(module+ test (require rackunit))

;;;; PCF に移行して reduction の拡張
;;;; ruleの中に書ける複数式の説明．通常の式以外に ≔ や #:when
;;;; ここで reduction の拡張も説明．

(define-language PCF₀ #:super LAM
  [M ∷= ....
     #t #f
     N
     `(+ ,M₁ ,M₂)
     `(<= ,M₁ ,M₂)
     `(if ,M₁ ,M₂ ,M₃)
     `(fix ,M)]
  [N ∷= (? number?)]
  [KWD ∷= .... '+ '<= 'if 'fix])

;; Mの定義が更新しているため「動的スコープ」で再定義
(define/match (subst n x m) #:super LAM:subst)

(define-reduction (-->PCF₀) #:super [(-->LAM)]
  [`(+ ,N₁ ,N₂) (+ N₁ N₂) "add"]
  [`(<= ,N₁ ,N₂)
   M ≔ (<= N₁ N₂)
   M
   "le"]
  [`(if #f ,M₂ ,M₃) M₃ "if-false"]
  [`(if ,M₁ ,M₂ ,M₃)
   #:when (not (false? M₁))
   M₂ "if-true"]
  [`(fix (λ (,X) ,M))
   X′ ≔ (gensym X)
   `((λ (,X) ,M) (λ (,X′) ((fix (λ (,X) ,M)) ,X′)))
   "fix"])

(define step-->PCF₀ (call-with-values (λ () (-->PCF₀)) compose1))
(define -->>PCF₀ (compose1 car (repeated step-->PCF₀)))

(module+ test
  ;(printf "---- PCF₀ -------------\n")
  ;; superの機能維持
  (check-equal? (-->>PCF₀ '((λ (x) x) (λ (z) (z z))))
                (set '(λ (z) (z z))))
  #;
  (check-equal?
   (-->>PCF₀ '((λ (x) (λ (z) (x z))) (λ (z) (x z))))
   (set '(λ (z787758) ((λ (z) (x z)) z787758))))
  ;;
  (check-equal? (step-->PCF₀ '(+ 1 2)) (set 3))
  (check-equal? (step-->PCF₀ '(+ (+ 1 2) 3)) (set)) ;; これはまだ(eval cxtが必要)
  (check-equal? (step-->PCF₀ '(<= 1 2)) (set #t))
  (check-equal? (step-->PCF₀ '(<= 3 2)) (set #f))
  (check-equal? (step-->PCF₀ '(if #f 3 2)) (set 2))
  (check-equal? (step-->PCF₀ '(if #t 3 2)) (set 3))
  (check-equal? (step-->PCF₀ '(if 8 3 2)) (set 3))
  (check-equal? (step-->PCF₀ '(if (<= 10 8) 3 2)) (set 3)) ;; これもまだだが
                                                           ;; まちがって遷移してる
  #;
  (check-equal? (step-->PCF₀ '(fix (λ (x) x)))
                (set '((λ (x) x) (λ (y986678) ((fix (λ (x) x)) y986678)))))
  )

;;;; 実際には，rule body は nondet monad．← (bind)がある．
;;;;   別の遷移の reducer を埋め込める．
;;; 例：λ-calculus の evaluation context (Redexでは特別な記法)

(define-reduction (-->PCF₁)
  #:do [(define →PCF₀ (reducer-of (-->PCF₀)))]
  [`(if ,M₁ ,M₂ ,M₃)
   M₁′ ← (→PCF₀ M₁)
   `(if ,M₁′ ,M₂ ,M₃)
   "ECif"])

(define step-->PCF₁ (call-with-values (λ () (-->PCF₁)) compose1))
(define -->>PCF₁ (repeated step-->PCF₁))

(module+ test
  ;(printf "---- PCF₁ -------------\n")
  ;; 継承してないので上4つはできない．
  (check-equal? (car (-->>PCF₁ '(+ 1 2)))
                (set '(+ 1 2)))
  (check-equal? (car (-->>PCF₁ '(+ (+ 1 2) 3)))
                (set '(+ (+ 1 2) 3)))
  (check-equal? (car (-->>PCF₁ '(<= 1 2))) (set '(<= 1 2)))
  (check-equal? (car (-->>PCF₁ '(<= 3 2))) (set '(<= 3 2)))
  (check-equal? (step-->PCF₁ '(if #f 3 2)) (set))
  (check-equal? (step-->PCF₁ '(if #t 3 2)) (set))
  (check-equal? (step-->PCF₁ '(if 8 3 2)) (set))
  (check-equal? (step-->PCF₁ '(if (<= 10 8) 3 2)) (set '(if #f 3 2)))
  (check-equal? (car (-->>PCF₁ '(if #f 3 2)))
                (set '(if #f 3 2)))
  (check-equal? (car (-->>PCF₁ '(if #t 3 2)))
                (set '(if #t 3 2)))
  (check-equal? (car (-->>PCF₁ '(if 8 3 2)))
                (set '(if 8 3 2)))
  (check-equal? (car (-->>PCF₁ '(if (<= 10 8) 3 2)))
                (set '(if #f 3 2))))

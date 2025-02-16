#lang racket
(require lightstep/reduction lightstep/set
         rackunit)

 ;; test-reduction
(define-reduction (r1 p)
  [(p a b) (p a a)]
  [(p a b) (p b b)])
(define u1-1 (inst-reduction r1 list))
(define reducer1-1 (invoke-unit u1-1))
(check-equal? (reducer1-1 '(2 3)) (set '(2 2) '(3 3)))

(define u1-2 (inst-reduction r1 set))
(define reducer1-2 (invoke-unit u1-2))
(check-equal? (reducer1-2 (set 2 3)) (set (set 2) (set 3)))

(define-reduction (r2)
  [x x])
(define u2 (inst-reduction r2))
(define reducer2 (invoke-unit u2))
(check-equal? (reducer2 'foo) (set 'foo))
(check-equal? (reducer2 100) (set 100))

(define-reduction (r3) #:super (r2)
  [(? number? n) (+ n n)])
(define u3 (inst-reduction r3))
(define reducer3 (invoke-unit u3))
(check-equal? (reducer3 100) (set 100 200))

(define-reduction (r4) #:super (r3)
  [(? number? n) (* n n)])
(define u4 (inst-reduction r4))
(define reducer4 (invoke-unit u4))
(check-equal? (reducer4 100) (set 100 200 10000))

(define-reduction (r5)
  [`(,x ...) x])
(define u5 (inst-reduction r5))
(define reducer5 (invoke-unit u5))
(check-equal? (reducer5 '(4 5 6 7)) (set '(4 5 6 7)))

(define-reduction (r6) #:super (r5))
(define u6 (inst-reduction r6))
(define reducer6 (invoke-unit u6))
(check-equal? (reducer6 '(8 9 10)) (set '(8 9 10)))

(define-reduction (s1) #:super (r2)
  [(? number? x) (+ x x)]
  [(? number? x)
   #:when (< x 0)
   y ≔ (- x)
   y])
(define u-s1 (inst-reduction s1))
(define reducer-s1 (invoke-unit u-s1))
(check-equal? (reducer-s1 -8) (set -16 -8 8))
(check-equal? (reducer-s1 8) (set 16 8))

;;=============================================================================
;; test-reduction*

(define-reduction (r11)
  [(list a b) a]
  [(list a b) b])
(define u11 (inst-reduction r11))
(define reducer11 (invoke-unit u11))
(check-equal? (car (apply-reduction* reducer11 '(1 (2 3)))) (set 1 2 3))

(define-reduction (r12 p)
  [(p a b) a]
  [(p a b) b])
(define u12-1 (inst-reduction r12 vector))
(define reducer12-1 (invoke-unit u12-1))
(check-equal? (car (apply-reduction* reducer12-1 (vector 1 (vector 2 3))))
              (set 1 2 3))
(define u12-2 (inst-reduction r12 set))
(define reducer12-2 (invoke-unit u12-2))
(check-equal? (car (apply-reduction* reducer12-2 (set 1 (set 2 3))))
              (set 1 2 3))

;;=============================================================================
;; test-override

(define-reduction (r31)
  [x (add1 x) "add"])
(define-reduction (r32) #:super (r31)
  [x (add1 (add1 x)) "add"])
(define u32 (inst-reduction r32))
(define reducer32 (invoke-unit u32))
(check-equal? (reducer32 0) (set 2))


;;=============================================================================
;; test-assign

(define-reduction (r41 ≔₁)
  [x
   y ≔₁ x
   y])
(define u41 (inst-reduction r41 ≔))
(define reducer41 (invoke-unit u41))
(check-equal? (reducer41 123) (set 123))
(check-equal? (reducer41 (set 123 456)) (set (set 123 456)))

(define u42 (inst-reduction r41 ←))
(define reducer42 (invoke-unit u42))
(check-equal? (reducer42 (set 123 456)) (set 123 456))

(define-reduction (-->₁)
  [x (+ x 1)]
  [x (+ x 10)])
(define-reduction (-->₂)
  [x (+ x 2)]
  [x (+ x 20)]
  [x (+ x 200)])

(define-reduction (r43 -->)
  [x
   y ← (--> x)
   y])

(define u43-1 (inst-reduction r43 (invoke-unit (inst-reduction -->₁))))
(define reducer43-1 (invoke-unit u43-1))
(check-equal? (reducer43-1 0) (set 1 10))

(define u43-2 (inst-reduction r43 (invoke-unit (inst-reduction -->₂))))
(define reducer43-2 (invoke-unit u43-2))
(check-equal? (reducer43-2 0) (set 2 20 200))

;;=============================================================================
;; test-unit

(define-signature hoge^ (hoge))
(define-unit hoge@ (import) (export hoge^)
  (define (hoge) 'hoge))

(define-reduction (r51 p)
  #:import [hoge^]
  [(p a b) (p (hoge) a)]
  [(p a b) (p b (hoge))])
(define u51 (inst-reduction r51 list))
(define reducer51 (invoke-unit
                   (compound-unit
                    (import) (export)
                    (link (([h : hoge^]) hoge@)
                          (() u51 h)))))
(check-equal? (reducer51 '(2 3)) (set '(3 hoge) '(hoge 2)))

(define-reduction (r52) #:super (r51 list))
(define u52 (inst-reduction r52))
(define reducer52 (invoke-unit
                   (compound-unit
                    (import) (export)
                    (link (([h : hoge^]) hoge@)
                          (() u52 h)))))
(check-equal? (reducer52 '(2 3)) (set '(3 hoge) '(hoge 2)))

;;=============================================================================
;; test-unit-only

(define-signature gege^ (hoge gege))
(define-unit gege@ (import) (export gege^)
  (define (hoge) 'hoge)
  (define (gege) 'gege))

(define-reduction (r61 p)
  #:import [(only gege^ gege)]
  [(p a b) (p a (gege))]
  [(p a b) (p (gege) b)])
(define u61 (inst-reduction r61 set))
(define reducer61 (invoke-unit
                   (compound-unit
                    (import) (export)
                    (link (([g : gege^]) gege@)
                          (() u61 g)))))
(check-equal? (reducer61 (set 'hoge 'gege)) (set (set 'gege)
                                                 (set 'hoge 'gege)))

;;=============================================================================
;; test-default

(define-reduction (r71)
  #:default [x `(default ,x)]
  [(? number? n) n "special"])
(define u71 (inst-reduction r71))
(define reducer71 (invoke-unit u71))
(check-equal? (reducer71 8) (set 8))
(check-equal? (reducer71 'foo) (set '(default foo)))
(check-equal? (reducer71 '(1 2)) (set '(default (1 2))))

(define-reduction (r72) #:super (r71)
  [(? symbol? s) (symbol->string s) "special"])
(define u72 (inst-reduction r72))
(define reducer72 (invoke-unit u72))
(check-equal? (reducer72 8) (set '(default 8)))
(check-equal? (reducer72 'foo) (set "foo"))
(check-equal? (reducer72 '(1 2)) (set '(default (1 2))))

(define-reduction (r73)
  #:default [`(,x ...) `(default ,(car x))]
  [(? number? n) n "special"])
(define u73 (inst-reduction r73))
(define reducer73 (invoke-unit u73))
(check-equal? (reducer73 8) (set 8))
(check-equal? (reducer73 'foo) ∅)
(check-equal? (reducer73 '(1 2)) (set '(default 1)))

(define-reduction (r74) #:super (r73)
  [(? symbol? s) (symbol->string s) "special"])
(define u74 (inst-reduction r74))
(define reducer74 (invoke-unit u74))
(check-equal? (reducer74 8) ∅)
(check-equal? (reducer74 'foo) (set "foo"))
(check-equal? (reducer74 '(1 2)) (set '(default 1)))

(define-reduction (r75 p q)
  #:default [x `(p ,x)]
  [(? number? n) (+ n q) "special"])
(define u75 (inst-reduction r75 default 100))
(define reducer75 (invoke-unit u75))
(check-equal? (reducer75 8) (set 108))
(check-equal? (reducer75 'foo) (set '(default foo)))
(check-equal? (reducer75 '(1 2)) (set '(default (1 2))))

(define-reduction (r76 a b) #:super (r75 b a)
  [(? symbol? s) (symbol->string s) "special"])
(define u76 (inst-reduction r76 200 DEFAULT))
(define reducer76 (invoke-unit u76))
(check-equal? (reducer76 8) (set '(DEFAULT 8)))
(check-equal? (reducer76 'foo) (set "foo"))
(check-equal? (reducer76 '(1 2)) (set '(DEFAULT (1 2))))

;;=============================================================================
;; test-do

(define-reduction (r81 p)
  #:do [(define y (* p 111))
        (printf "printf in #:do: ~a ~a\n" p y)]
  [x (+ x y)])
(check-equal? ((invoke-unit (inst-reduction r81 2)) 888) (set 1110))

(define-reduction (r82 p)
  #:import [gege^]
  #:do [(printf "printf in #:do: ~a\n" (hoge))
        (define y (* p 111))]
  [x (list (gege) (+ x y))])
(define u82 (inst-reduction r82 3))
(define reducer82 (invoke-unit
                   (compound-unit
                    (import) (export)
                    (link (([g : gege^]) gege@)
                          (() u82 g)))))
(check-equal? (reducer82 888) (set '(gege 1221)))

;;=============================================================================
;; test-scope

(module+ scope1
  (provide r21)
  (define (add x) (+ x 1))
  (define-reduction (r21)
    [x (add x)])
  (define-reduction (r22) #:super (r21)
    [x (add (add x))])
  (define u22 (inst-reduction r22))
  (define reducer22 (invoke-unit u22))
  (check-equal? (reducer22 8) (set 9 10)))

(module+ scope2
  (require (submod ".." scope1))
  (define u21 (inst-reduction r21))
  (define reducer21 (invoke-unit u21))
  (check-equal? (reducer21 8) (set 9))

  (define (add x) (+ x 100))
  (define-reduction (r22) #:super (r21)
    [x (add (add x))])
  (define u22 (inst-reduction r22))
  (define reducer22 (invoke-unit u22))
  (check-equal? (reducer22 8) (set 108 208)))

#lang racket
(require lightstep/base
         (only-in lightstep/transformers
                  monad^ define-monad run-StateT StateT NondetT ID)
         (except-in rackunit fail))

 ;; test-reduction
(define-reduction (r1 p)
  [(p a b) (p a a)]
  [(p a b) (p b b)])
(define u1-1 (r1 list))
(define-values (mrun1-1 reducer1-1) (invoke-unit u1-1))
(define -->1-1 (compose1 mrun1-1 reducer1-1))
(check-equal? (-->1-1 '(2 3)) (set '(2 2) '(3 3)))

(define u1-2 (r1 set))
(define-values (mrun1-2 reducer1-2) (invoke-unit u1-2))
(define -->1-2 (compose1 mrun1-2 reducer1-2))
(check-equal? (-->1-2 (set 2 3)) (set (set 2) (set 3)))

(define-reduction (r2)
  [x x])
(define-values (mrun2 reducer2) (invoke-unit (r2)))
(define -->2 (compose1 mrun2 reducer2))
(check-equal? (-->2 'foo) (set 'foo))
(check-equal? (-->2 100) (set 100))

(define-reduction (r3) #:super (r2)
  [(? number? n) (+ n n)])
(define-values (mrun3 reducer3) (invoke-unit (r3)))
(define -->3 (compose1 mrun3 reducer3))
(check-equal? (-->3 100) (set 100 200))

(define-reduction (r4) #:super (r3)
  [(? number? n) (* n n)])
(define-values (mrun4 reducer4) (invoke-unit (r4)))
(define -->4 (compose1 mrun4 reducer4))
(check-equal? (-->4 100) (set 100 200 10000))

(define-reduction (r5)
  [`(,x ...) x])
(define-values (mrun5 reducer5) (invoke-unit (r5)))
(define -->5 (compose1 mrun5 reducer5))
(check-equal? (-->5 '(4 5 6 7)) (set '(4 5 6 7)))

(define-reduction (r6) #:super (r5))
(define-values (mrun6 reducer6) (invoke-unit (r6)))
(define -->6 (compose1 mrun6 reducer6))
(check-equal? (-->6 '(8 9 10)) (set '(8 9 10)))

(define-reduction (s1) #:super (r2)
  [(? number? x) (+ x x)]
  [(? number? x)
   #:when (< x 0)
   y ≔ (- x)
   y])
(define-values (mrun-s1 reducer-s1) (invoke-unit (s1)))
(define -->s1 (compose1 mrun-s1 reducer-s1))
(check-equal? (-->s1 -8) (set -16 -8 8))
(check-equal? (-->s1 8) (set 16 8))

;;=============================================================================
;; test-repeated

(define-reduction (r11)
  [(list a b) a]
  [(list a b) b])
(define-values (mrun11 reducer11) (invoke-unit (r11)))
(define -->11 (compose1 mrun11 reducer11))
(check-equal? (car ((repeated -->11) '(1 (2 3)))) (set 1 2 3))

(define-reduction (r12 p)
  [(p a b) a]
  [(p a b) b])
(define u12-1 (r12 vector))
(define-values (mrun12-1 reducer12-1) (invoke-unit u12-1))
(define -->12-1 (compose1 mrun12-1 reducer12-1))
(check-equal? (car ((repeated -->12-1) (vector 1 (vector 2 3))))
              (set 1 2 3))
(define u12-2 (r12 set))
(define-values (mrun12-2 reducer12-2) (invoke-unit u12-2))
(define -->12-2 (compose1 mrun12-2 reducer12-2))
(check-equal? (car ((repeated -->12-2) (set 1 (set 2 3))))
              (set 1 2 3))

;;=============================================================================
;; test-override

(define-reduction (r31)
  [x (add1 x) "add"])
(define-reduction (r32) #:super (r31)
  [x (add1 (add1 x)) "add"])
(define-values (mrun32 reducer32) (invoke-unit (r32)))
(define -->32 (compose1 mrun32 reducer32))
(check-equal? (-->32 0) (set 2))


;;=============================================================================
;; test-assign

(define-reduction (r41 ≔₁)
  [x
   y ≔₁ x
   y])
(define-values (mrun41 reducer41) (invoke-unit (r41 ≔)))
(define -->41 (compose1 mrun41 reducer41))
(check-equal? (-->41 123) (set 123))
(check-equal? (-->41 (set 123 456)) (set (set 123 456)))

(define-values (mrun42 reducer42) (invoke-unit (r41 ←)))
(define -->42 (compose1 mrun42 reducer42))
(check-equal? (-->42 (set 123 456)) (set 123 456))

(define-reduction (-->₁rule)
  [x (+ x 1)]
  [x (+ x 10)])
(define-reduction (-->₂rule)
  [x (+ x 2)]
  [x (+ x 20)]
  [x (+ x 200)])

(define-reduction (r43 -->)
  [x
   y ← (--> x)
   y])

(define u43-1 (r43 (call-with-values
                    (λ () (invoke-unit (-->₁rule)))
                    (λ (_mrun reducer) reducer))))
(define-values (mrun43-1 reducer43-1) (invoke-unit u43-1))
(define -->43-1 (compose1 mrun43-1 reducer43-1))
(check-equal? (-->43-1 0) (set 1 10))

(define u43-2 (r43 (call-with-values
                    (λ () (invoke-unit (-->₂rule)))
                    (λ (_mrun reducer) reducer))))
(define-values (mrun43-2 reducer43-2) (invoke-unit u43-2))
(define -->43-2 (compose1 mrun43-2 reducer43-2))
(check-equal? (-->43-2 0) (set 2 20 200))


(define-reduction (r44)
  [x
   (cons (? number? n) (? number? m)) ≔ x
   (+ n m)]
  [x
   (? number? n) ← (return x)
   (* n n)]
  [x
   #t ← (return x)
   'TRUE]
  [x x])
(define-values (mrun44 reducer44) (invoke-unit (r44)))
(define -->44 (compose1 mrun44 reducer44))
(check-equal? (-->44 8) (set 8 64))
(check-equal? (-->44 'foo) (set 'foo))
(check-equal? (-->44 (cons 3 7)) (set (cons 3 7) 10))
(check-equal? (-->44 #t) (set #t 'TRUE))

;;=============================================================================
;; test-unit

(define-signature hoge^ (hoge))
(define-unit hoge@ (import) (export hoge^)
  (define (hoge) 'hoge))

(define-reduction (r51 p)
  #:import [hoge^]
  [(p a b) (p (hoge) a)]
  [(p a b) (p b (hoge))])
(define-values (mrun51 reducer51) (invoke-unit
                                   (compound-unit
                                    (import) (export)
                                    (link (([h : hoge^]) hoge@)
                                          (() (r51 list) h)))))
(define -->51 (compose1 mrun51 reducer51))
(check-equal? (-->51 '(2 3)) (set '(3 hoge) '(hoge 2)))

(define-reduction (r52) #:super (r51 list))
(define-values (mrun52 reducer52) (invoke-unit
                                   (compound-unit
                                    (import) (export)
                                    (link (([h : hoge^]) hoge@)
                                          (() (r52) h)))))
(define -->52 (compose1 mrun52 reducer52))
(check-equal? (-->52 '(2 3)) (set '(3 hoge) '(hoge 2)))

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
(define-values (mrun61 reducer61) (invoke-unit
                                   (compound-unit
                                    (import) (export)
                                    (link (([g : gege^]) gege@)
                                          (() (r61 set) g)))))
(define -->61 (compose1 mrun61 reducer61))
(check-equal? (-->61 (set 'hoge 'gege)) (set (set 'gege)
                                             (set 'hoge 'gege)))

;;=============================================================================
;; test-default

(define-reduction (r71)
  #:default [x `(default ,x)]
  [(? number? n) n "special"])
(define-values (mrun71 reducer71) (invoke-unit (r71)))
(define -->71 (compose1 mrun71 reducer71))
(check-equal? (-->71 8) (set 8))
(check-equal? (-->71 'foo) (set '(default foo)))
(check-equal? (-->71 '(1 2)) (set '(default (1 2))))

(define-reduction (r72) #:super (r71)
  [(? symbol? s) (symbol->string s) "special"])
(define-values (mrun72 reducer72) (invoke-unit (r72)))
(define -->72 (compose1 mrun72 reducer72))
(check-equal? (-->72 8) (set '(default 8)))
(check-equal? (-->72 'foo) (set "foo"))
(check-equal? (-->72 '(1 2)) (set '(default (1 2))))

(define-reduction (r73)
  #:default [`(,x ...) `(default ,(car x))]
  [(? number? n) n "special"])
(define-values (mrun73 reducer73) (invoke-unit (r73)))
(define -->73 (compose1 mrun73 reducer73))
(check-equal? (-->73 8) (set 8))
(check-equal? (-->73 'foo) ∅)
(check-equal? (-->73 '(1 2)) (set '(default 1)))

(define-reduction (r74) #:super (r73)
  [(? symbol? s) (symbol->string s) "special"])
(define-values (mrun74 reducer74) (invoke-unit (r74)))
(define -->74 (compose1 mrun74 reducer74))
(check-equal? (-->74 8) ∅)
(check-equal? (-->74 'foo) (set "foo"))
(check-equal? (-->74 '(1 2)) (set '(default 1)))

(define-reduction (r75 p q)
  #:default [x `(p ,x)]
  [(? number? n) (+ n q) "special"])
(define-values (mrun75 reducer75) (invoke-unit (r75 default 100)))
(define -->75 (compose1 mrun75 reducer75))
(check-equal? (-->75 8) (set 108))
(check-equal? (-->75 'foo) (set '(default foo)))
(check-equal? (-->75 '(1 2)) (set '(default (1 2))))

(define-reduction (r76 a b) #:super (r75 b a)
  [(? symbol? s) (symbol->string s) "special"])
(define-values (mrun76 reducer76) (invoke-unit (r76 200 DEFAULT)))
(define -->76 (compose1 mrun76 reducer76))
(check-equal? (-->76 8) (set '(DEFAULT 8)))
(check-equal? (-->76 'foo) (set "foo"))
(check-equal? (-->76 '(1 2)) (set '(DEFAULT (1 2))))

;;=============================================================================
;; test-do

(define-reduction (r81 p)
  #:do [(define y (* p 111))
        ;(printf "printf in #:do: ~a ~a\n" p y)
        ]
  [x (+ x y)])
(check-equal? (call-with-values
                (λ () (invoke-unit (r81 2)))
                (λ (mrun reducer)
                  (mrun (reducer 888))))
              (set 1110))

(define-reduction (r82 p)
  #:import [gege^]
  #:do [;(printf "printf in #:do: ~a\n" (hoge))
        (define y (* p 111))]
  [x (list (gege) (+ x y))])
(define-values (mrun82 reducer82) (invoke-unit
                                   (compound-unit
                                    (import) (export)
                                    (link (([g : gege^]) gege@)
                                          (() (r82 3) g)))))
(define -->82 (compose1 mrun82 reducer82))
(check-equal? (-->82 888) (set '(gege 1221)))

;;=============================================================================
;; test-monad

(define-reduction (r91)
  #:monad (StateT #f (NondetT ID))
  ;; #:mrun (λ (m) (run-StateT (set 'a 'b 'c) m))
  [x
   `(,_ ,y ...) ← (return x)
   σ ← get
   (put (for/set ([v σ]) (cons v v)))
   (list y σ)]
  [(list a b c) (+ a b c)])
(define-values (mrun91 reducer91) (invoke-unit (r91)))
(define -->91 (compose1 (λ (m) (mrun91 (set 'a 'b 'c) m)) reducer91))
(check-equal? (-->91 '(1 2 3))
              (set (cons 6 (set 'a 'b 'c))
                   (cons (list '(2 3) (set 'a 'b 'c))
                         (set (cons 'a 'a) (cons 'b 'b) (cons 'c 'c)))))

(define-reduction (r92)
  [(? number? n) n "id"]
  [(? number? n) (+ n 92)])

(define-reduction (r93) #:super (r92)
  [(? number? n)
   #:when (< n 0)
   (- n) "id"])
(define-values (mrun93 reducer93) (invoke-unit (r93)))
(define -->93 (compose1 mrun93 reducer93))
(check-equal? (-->93 -2) (set 2 90))

(define-reduction (r94) #:super (r92)
  #:monad (StateT #f (NondetT ID))
  ;; #:mrun (λ (M σ) (run-StateT σ M))
  [(? number? n)
   #:when (< n 0)
   (- n) "id"])
(define-values (mrun94 reducer94) (invoke-unit (r94)))
(define (-->94 e σ) (mrun94 σ (reducer94 e)))
(check-equal? (-->94 -2 ∅) (set (cons 2 ∅) (cons 90 ∅)))


(define-unit r95@
  (import monad^) (export)
  (define-monad M)

  (define-reduction (r95)
    #:monad M
    #:mrun mrun
    [x
     σ ← get
     (put (σ 'Y x))
     xσ ← (return (list x (σ 'X x)))
     xσ])
  (define-values (mrun95 reducer95) (invoke-unit (r95)))
  (define -->95 (compose1 mrun95 reducer95))
  -->95)

(define-unit m95@
  (import) (export monad^)
  (define M (StateT #f (NondetT ID)))
  (define (mrun m) (run-StateT map-∅ m)))

(define -->95 (invoke-unit (compound-unit
                            (import) (export)
                            (link (([m : monad^]) m95@)
                                  (() r95@ m)))))
(check-equal? (-->95 888) (set (cons (list 888 (↦ ['X 888])) (↦ ['Y 888]))))


;;=============================================================================
;; test-scope

(module+ scope1
  (provide r21)
  (define (add x) (+ x 1))
  (define-reduction (r21)
    [x (add x)])
  (define-reduction (r22) #:super (r21)
    [x (add (add x))])
  (define-values (mrun22 reducer22) (invoke-unit (r22)))
  (define -->22 (compose1 mrun22 reducer22))
  (check-equal? (-->22 8) (set 9 10)))

(module+ scope2
  (require (only-in (submod ".." scope1) r21))
  (define-values (mrun21 reducer21) (invoke-unit (r21)))
  (define -->21 (compose1 mrun21 reducer21))
  (check-equal? (-->21 8) (set 9))

  (define (add x) (+ x 100))
  (define-reduction (r22) #:super (r21)
    [x (add (add x))])
  (define-values (mrun22 reducer22) (invoke-unit (r22)))
  (define -->22 (compose mrun22 reducer22))
  (check-equal? (-->22 8) (set 108 208)))

;;=============================================================================
;; test-inject-set-into-nondet

(define-reduction (r100)
  #:monad (StateT #f (NondetT ID))
  [x
   σ ← get
   s ← (for/monad+ ([s σ]) (return s))
   (put ∅)
   (list s x)])
(define -->100 (call-with-values
                (λ () (invoke-unit (r100)))
                (λ (mrun reducer) (λ (σ x) (mrun σ (reducer x))))))
(check-equal? (-->100 (set 'a 'b 'c) 888)
              (set (cons '(a 888) ∅)
                   (cons '(b 888) ∅)
                   (cons '(c 888) ∅)))

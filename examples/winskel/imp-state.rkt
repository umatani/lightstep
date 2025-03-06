#lang racket/base
(require lightstep/base
         (only-in lightstep/transformers
                  with-monad run-StateT StateT NondetT ID)
         (only-in racket/match match-define))

(module+ test (require rackunit))

;;=============================================================================
;; 2.2 The evaluation of arithmetic expressions

(define-reduction (-->a)
  #:monad (StateT #f (NondetT ID))

  [(? number? n)
   n
   "number"]

  [(? symbol? X)
   σ ← get
   (σ X)
   "location"]

  [`(+ ,a₀ ,a₁)
   n₀ ← (-->a a₀)
   n₁ ← (-->a a₁)
   (+ n₀ n₁)
   "sum"]

  [`(- ,a₀ ,a₁)
   n₀ ← (-->a a₀)
   n₁ ← (-->a a₁)
   (- n₀ n₁)
   "subtract"]

  [`(× ,a₀ ,a₁)
   n₀ ← (-->a a₀)
   n₁ ← (-->a a₁)
   (* n₀ n₁)
   "product"])

(define (step-a a [σ (↦)])
  (define-values (mrun reducer) (-->a))
  (mrun σ (reducer a)))

(define ((~a a₀ a₁) σ)
  (equal? (step-a a₀ σ) (step-a a₁ σ)))

(module+ test
  (define σ (↦ ['x 3] ['y 2]))

  (check-equal? (step-a 3) (set (cons 3 (↦))))
  (check-equal? (step-a 'y σ) (set (cons 2 σ)))
  (check-equal? (step-a '(+ x 1) σ) (set (cons 4 σ)))
  (check-equal? (step-a '(+ x y) σ) (set (cons 5 σ)))
  (check-equal? (step-a '(- x y) σ) (set (cons 1 σ)))
  (check-equal? (step-a '(× x y) σ) (set (cons 6 σ)))

  (check-equal? (step-a '(+ (+ Init 5) (+ 7 9)) (↦ ['Init 0]))
                (set (cons 21 (↦ ['Init 0])))))

;;=============================================================================
;; 2.3 The evaluation of boolean expressions

(define-reduction (-->b -->a)
  #:monad (StateT #f (NondetT ID))

  [#t
   #t
   "true"]

  [#f
   #f
   "false"]

  [`(= ,a₀ ,a₁)
   n ← (-->a a₀)
   m ← (-->a a₁)
   #:when (= n m)
   #t
   "equal"]

  [`(= ,a₀ ,a₁)
   n ← (-->a a₀)
   m ← (-->a a₁)
   #:unless (= n m)
   #f
   "not equal"]

  [`(≤ ,a₀ ,a₁)
   n ← (-->a a₀)
   m ← (-->a a₁)
   #:when (<= n m)
   #t
   "less than or equal"]

  [`(≤ ,a₀ ,a₁)
   n ← (-->a a₀)
   m ← (-->a a₁)
   #:unless (<= n m)
   #f
   "not less than or equal"]

  [`(¬ ,b)
   #t ← (-->b b)
   #f
   "not-true"]

  [`(¬ ,b)
   #f ← (-->b b)
   #t
   "not-false"]

  [`(∧ ,b₀ ,b₁)
   t₀ ← (-->b b₀)
   t₁ ← (-->b b₁)
   (and t₀ t₁)
   "and"]

  [`(∨ ,b₀ ,b₁)
   t₀ ← (-->b b₀)
   t₁ ← (-->b b₁)
   (or t₀ t₁)
   "or"])

(define (step-b b [σ (↦)])
  (define-values (mrun reducer) (-->b (reducer-of (-->a))))
  (mrun σ (reducer b)))

(define ((~b b₀ b₁) σ)
  (equal? (step-b b₀ σ) (step-b b₁ σ)))

(module+ test
  (check-equal? (step-b #t) (set (cons #t (↦))))
  (check-equal? (step-b #f) (set (cons #f (↦))))
  (check-equal? (step-b '(= x 1) (↦ ['x 1])) (set (cons #t (↦ ['x 1]))))
  (check-equal? (step-b '(= x 1) (↦ ['x 2])) (set (cons #f (↦ ['x 2]))))
  (check-equal? (step-b '(≤ x 0) (↦ ['x 1])) (set (cons #f (↦ ['x 1]))))
  (check-equal? (step-b '(≤ x 3) (↦ ['x 2])) (set (cons #t (↦ ['x 2]))))
  (check-equal? (step-b '(¬ (≤ x 0)) (↦ ['x 1])) (set (cons #t (↦ ['x 1]))))
  (check-equal? (step-b '(¬ (≤ x 3)) (↦ ['x 2])) (set (cons #f (↦ ['x 2]))))
  (check-equal? (step-b '(∧ (≤ x 0) (≤ x 3)) (↦ ['x 1]))
                (set (cons #f (↦ ['x 1]))))
  (check-equal? (step-b '(∧ (≤ x 2) (≤ x 3)) (↦ ['x 1]))
                (set (cons #t (↦ ['x 1]))))
  (check-equal? (step-b '(∨ (≤ x -1) (≤ x 0)) (↦ ['x 1]))
                (set (cons #f (↦ ['x 1]))))
  (check-equal? (step-b '(∨ (≤ x 0) (≤ x 3)) (↦ ['x 1]))
                (set (cons #t (↦ ['x 1]))))
  (check-equal? (step-b '(∨ (≤ x 2) (≤ x 3)) (↦ ['x 1]))
                (set (cons #t (↦ ['x 1])))))

(module+ left-first-sequential
  (require rackunit)

  (define-reduction (-->b′ -->a) #:super [(-->b -->a)]
    #:monad (StateT #f (NondetT ID))

    ;; remove super's "and" rule
    [`(∧ ,b₀ ,b₁)
     #:when #f
     (void)
     "and"]

    [`(∧ ,b₀ ,b₁)
     #f ← (-->b′ b₀)
     #f
     "and-f"]

    [`(∧ ,b₀ ,b₁)
     #t ← (-->b′ b₀)
     #f ← (-->b′ b₁)
     #f
     "and-tf"]

    [`(∧ ,b₀ ,b₁)
     #t ← (-->b′ b₀)
     #t ← (-->b′ b₁)
     #t
     "and-tt"]

    ;; remove super's "or" rule
    [`(∨ ,b₀ ,b₁)
     #:when #f
     (void)
     "or"]

    [`(∨ ,b₀ ,b₁)
     #t ← (-->b′ b₀)
     #t
     "or-t"]

    [`(∨ ,b₀ ,b₁)
     #f ← (-->b′ b₀)
     #t ← (-->b′ b₁)
     #t
     "or-ft"]

    [`(∨ ,b₀ ,b₁)
     #f ← (-->b′ b₀)
     #f ← (-->b′ b₁)
     #f
     "or-ff"])

  (define (step-b′ b [σ (↦)])
    (define-values (mrun reducer) (-->b′ (reducer-of (-->a))))
    (mrun σ (reducer b)))

  (check-equal? (step-b′ #t) (set (cons #t (↦))))
  (check-equal? (step-b′ #f) (set (cons #f (↦))))
  (check-equal? (step-b′ '(= x 1) (↦ ['x 1])) (set (cons #t (↦ ['x 1]))))
  (check-equal? (step-b′ '(= x 1) (↦ ['x 2])) (set (cons #f (↦ ['x 2]))))
  (check-equal? (step-b′ '(≤ x 0) (↦ ['x 1])) (set (cons #f (↦ ['x 1]))))
  (check-equal? (step-b′ '(≤ x 3) (↦ ['x 2])) (set (cons #t (↦ ['x 2]))))
  (check-equal? (step-b′ '(¬ (≤ x 0)) (↦ ['x 1])) (set (cons #t (↦ ['x 1]))))
  (check-equal? (step-b′ '(¬ (≤ x 3)) (↦ ['x 2])) (set (cons #f (↦ ['x 2]))))
  (check-equal? (step-b′ '(∧ (≤ x 0) (≤ x 3)) (↦ ['x 1]))
                (set (cons #f (↦ ['x 1]))))
  (check-equal? (step-b′ '(∧ (≤ x 2) (≤ x 3)) (↦ ['x 1]))
                (set (cons #t (↦ ['x 1]))))
  (check-equal? (step-b′ '(∨ (≤ x -1) (≤ x 0)) (↦ ['x 1]))
                (set (cons #f (↦ ['x 1]))))
  (check-equal? (step-b′ '(∨ (≤ x 0) (≤ x 3)) (↦ ['x 1]))
                (set (cons #t (↦ ['x 1]))))
  (check-equal? (step-b′ '(∨ (≤ x 2) (≤ x 3)) (↦ ['x 1]))
                (set (cons #t (↦ ['x 1])))))

(module+ parallel-or
  (require rackunit)

  (define-reduction (-->b′ -->a) #:super [(-->b -->a)]
    #:monad (StateT #f (NondetT ID))

    ;; remove super's "or" rule
    [`(∨ ,b₀ ,b₁)
     #:when #f
     (void)
     "or"]

    [`(∨ ,b₀ ,b₁)
     #t ← (-->b′ b₀)
     #t
     "or-l"]

    [`(∨ ,b₀ ,b₁)
     #t ← (-->b′ b₁)
     #t
     "or-r"]

    [`(∨ ,b₀ ,b₁)
     #f ← (-->b′ b₀)
     #f ← (-->b′ b₁)
     #f
     "or-ff"])

  (define (step-b′ b [σ (↦)])
    (define-values (mrun reducer) (-->b′ (reducer-of (-->a))))
    (mrun σ (reducer b)))

  (check-equal? (step-b′ #t) (set (cons #t (↦))))
  (check-equal? (step-b′ #f) (set (cons #f (↦))))
  (check-equal? (step-b′ '(= x 1) (↦ ['x 1])) (set (cons #t (↦ ['x 1]))))
  (check-equal? (step-b′ '(= x 1) (↦ ['x 2])) (set (cons #f (↦ ['x 2]))))
  (check-equal? (step-b′ '(≤ x 0) (↦ ['x 1])) (set (cons #f (↦ ['x 1]))))
  (check-equal? (step-b′ '(≤ x 3) (↦ ['x 2])) (set (cons #t (↦ ['x 2]))))
  (check-equal? (step-b′ '(¬ (≤ x 0)) (↦ ['x 1])) (set (cons #t (↦ ['x 1]))))
  (check-equal? (step-b′ '(¬ (≤ x 3)) (↦ ['x 2])) (set (cons #f (↦ ['x 2]))))
  (check-equal? (step-b′ '(∧ (≤ x 0) (≤ x 3)) (↦ ['x 1]))
                (set (cons #f (↦ ['x 1]))))
  (check-equal? (step-b′ '(∧ (≤ x 2) (≤ x 3)) (↦ ['x 1]))
                (set (cons #t (↦ ['x 1]))))
  (check-equal? (step-b′ '(∨ (≤ x -1) (≤ x 0)) (↦ ['x 1]))
                (set (cons #f (↦ ['x 1]))))
  (check-equal? (step-b′ '(∨ (≤ x 0) (≤ x 3)) (↦ ['x 1]))
                (set (cons #t (↦ ['x 1]))))
  (check-equal? (step-b′ '(∨ (≤ x 2) (≤ x 3)) (↦ ['x 1]))
                (set (cons #t (↦ ['x 1])))))


;;=============================================================================
;; 2.4 The execution of commands

(define-reduction (-->c -->a -->b)
  #:monad (StateT #f (NondetT ID))

  ['skip
   σ ← get
   σ
   "skip"]

  [`(≔ ,x ,a)
   m ← (-->a a)
   σ ← get
   σ′ ≔ (σ x m)
   (put σ′)
   σ′
   "assign"]

  [`(seq ,c₀ ,c₁)
   (-->c c₀) 
   (-->c c₁)
   σ ← get
   σ
   "seq"]

  [`(if ,b ,c₀ ,c₁)
   #t ← (-->b b)
   (-->c c₀)
   σ ← get
   σ
   "if-t"]

  [`(if ,b ,c₀ ,c₁)
   #f ← (-->b b)
   (-->c c₁)
   σ ← get
   σ
   "if-f"]

  [`(while ,b ,c)
   #f ← (-->b b)
   σ ← get
   σ
   "while-f"]

  [`(while ,b ,c)
   #t ← (-->b b)
   (-->c c)
   (-->c `(while ,b ,c))
   σ ← get
   σ
   "while-t"])

(define (step-c c [σ (↦)])
  (define reducer-a (reducer-of (-->a)))
  (define-values (mrun reducer) (-->c reducer-a (reducer-of (-->b reducer-a))))
  (for/set ([vσ (mrun σ (reducer c))])
    (car vσ)))

(define ((~c c₀ c₁) σ)
  (equal? (step-c c₀ σ) (step-c c₁ σ)))

(module+ test
  (check-equal? (step-c 'skip (↦ ['x 1]))
                (set          (↦ ['x 1])))
  (check-equal? (step-c '(≔ x (+ x 1)) (↦ ['x 1]))
                (set                   (↦ ['x 2])))
  (check-equal? (step-c '(seq (≔ x (+ x 1)) (≔ y (+ y x))) (↦ ['x 1] ['y 1]))
                (set                                       (↦ ['x 2] ['y 3])))
  (check-equal? (step-c '(if (≤ x 1)
                           (≔ x (+ x 1))
                           skip)
                        (↦ ['x 1]))
                (set    (↦ ['x 2])))
  (check-equal? (step-c '(if (≤ x 1)
                           (≔ x (+ x 1))
                           skip)
                        (↦ ['x 2]))
                (set    (↦ ['x 2])))
  (check-equal? (step-c '(while (¬ (= x 0))
                           (seq (≔ sum (+ sum x))
                                (≔ x (- x 1))))
                        (↦ ['x 10] ['sum  0]))
                (set    (↦ ['x  0] ['sum 55]))))


;;=============================================================================
;; 2.6 Alternative semantics

(define-reduction (-->₁a)
  #:monad (StateT #f (NondetT ID))

  [(? symbol? X)
   σ ← get
   (σ X)]

  [`(+ ,a₀ ,a₁)
   a₀′ ← (-->₁a a₀)
   `(+ ,a₀′ ,a₁)]

  [`(+ ,(? number? n₀) ,a₁)
   a₁′ ← (-->₁a a₁)
   `(+ ,n₀ ,a₁′)]

  [`(+ ,(? number? n₀) ,(? number? n₁))
   (+ n₀ n₁)]

  [`(- ,a₀ ,a₁)
   a₀′ ← (-->₁a a₀)
   `(- ,a₀′ ,a₁)]

  [`(- ,(? number? n₀) ,a₁)
   a₁′ ← (-->₁a a₁)
   `(- ,n₀ ,a₁′)]

  [`(- ,(? number? n₀) ,(? number? n₁))
   (- n₀ n₁)]

  [`(× ,a₀ ,a₁)
   a₀′ ← (-->₁a a₀)
   `(× ,a₀′ ,a₁)]

  [`(× ,(? number? n₀) ,a₁)
   a₁′ ← (-->₁a a₁)
   `(× ,n₀ ,a₁′)]

  [`(× ,(? number? n₀) ,(? number? n₁))
   (* n₀ n₁)])

(define (step₁-a aσ)
  (define-values (mrun reducer) (-->₁a))
  (match-define (cons a σ) aσ)
  (mrun σ (reducer a)))
(define -->>₁a (repeated step₁-a))

(define ((~₁a a₀ a₁) σ)
  (equal? (step₁-a (cons a₀ σ)) (step₁-a (cons a₁ σ))))

(module+ test
  (check-equal? (step₁-a (cons 3 (↦))) ∅)
  (check-equal? (step₁-a (cons 'y σ))
                (set     (cons 2  σ)))
  (check-equal? (step₁-a (cons '(+ x 1) σ))
                (set     (cons '(+ 3 1) σ)))
  (check-equal? (step₁-a (cons '(+ x y) σ))
                (set     (cons '(+ 3 y) σ)))
  (check-equal? (step₁-a (cons '(- x y) σ))
                (set     (cons '(- 3 y) σ)))
  (check-equal? (step₁-a (cons '(× x y) σ))
                (set     (cons '(× 3 y) σ)))
  (check-equal? (step₁-a (cons '(+ (+ Init 5) (+ 7 9)) (↦ ['Init 0])))
                (set     (cons '(+ (+ 0    5) (+ 7 9)) (↦ ['Init 0]))))

  (check-equal? (car (-->>₁a (cons 3 (↦))))
                (set         (cons 3 (↦))))
  (check-equal? (car (-->>₁a (cons 'y σ)))
                (set         (cons 2  σ)))
  (check-equal? (car (-->>₁a (cons '(+ x 1) σ)))
                (set         (cons 4        σ)))
  (check-equal? (car (-->>₁a (cons '(+ x y) σ)))
                (set         (cons 5        σ)))
  (check-equal? (car (-->>₁a (cons '(- x y) σ)))
                (set         (cons 1        σ)))
  (check-equal? (car (-->>₁a (cons '(× x y) σ)))
                (set         (cons 6        σ)))
  (check-equal? (car (-->>₁a (cons '(+ (+ Init 5) (+ 7 9)) (↦ ['Init 0]))))
                (set         (cons 21                      (↦ ['Init 0])))))


(define-reduction (-->₁b -->₁a)
  #:monad (StateT #f (NondetT ID))

  [`(= ,a₀ ,a₁)
   a₀′ ← (-->₁a a₀)
   `(= ,a₀′ ,a₁)]

  [`(= ,(? number? n) ,a₁)
   a₁′ ← (-->₁a a₁)
   `(= ,n ,a₁′)]

  [`(= ,(? number? n) ,(? number? m))
   #:when (= n m)
   #t]

  [`(= ,(? number? n) ,(? number? m))
   #:unless (= n m)
   #f]

  [`(≤ ,a₀ ,a₁)
   a₀′ ← (-->₁a a₀)
   `(≤ ,a₀′ ,a₁)]

  [`(≤ ,(? number? n) ,a₁)
   a₁′ ← (-->₁a a₁)
   `(≤ ,n ,a₁′)]

  [`(≤ ,(? number? n) ,(? number? m))
   #:when (<= n m)
   #t]

  [`(≤ ,(? number? n) ,(? number? m))
   #:unless (<= n m)
   #f]

  [`(¬ ,b)
   b′ ← (-->₁b b)
   `(¬ ,b′)]

  ['(¬ #t)
   #f]

  ['(¬ #f)
   #t]

  [`(∧ ,b₀ ,b₁)
   b₀′ ← (-->₁b b₀)
   `(∧ ,b₀′ ,b₁)]

  [`(∧ ,(? boolean? t₀) ,b₁)
   b₁′ ← (-->₁b b₁)
   `(∧ ,t₀ ,b₁′)]

  [`(∧ ,(? boolean? t₀) ,(? boolean? t₁))
   (and t₀ t₁)]

  [`(∨ ,b₀ ,b₁)
   b₀′ ← (-->₁b b₀)
   `(∨ ,b₀′ ,b₁)]

  [`(∨ ,(? boolean? t₀) ,b₁)
   b₁′ ← (-->₁b b₁)
   `(∨ ,t₀ ,b₁′)]

  [`(∨ ,(? boolean? t₀) ,(? boolean? t₁))
   (or t₀ t₁)])

(define (step₁-b bσ)
  (define-values (mrun reducer) (-->₁b (reducer-of (-->₁a))))
  (match-define (cons b σ) bσ)
  (mrun σ (reducer b)))
(define -->>₁b (repeated step₁-b))

(define ((~₁b b₀ b₁) σ)
  (equal? (step₁-b (cons b₀ σ)) (step₁-b (cons b₁ σ))))

(module+ test
  (check-equal? (step₁-b (cons #t (↦))) ∅)
  (check-equal? (step₁-b (cons #f (↦))) ∅)
  (check-equal? (step₁-b (cons '(= x 1) (↦ ['x 1])))
                (set     (cons '(= 1 1) (↦ ['x 1]))))
  (check-equal? (step₁-b (cons '(= x 1) (↦ ['x 2])))
                (set     (cons '(= 2 1) (↦ ['x 2]))))
  (check-equal? (step₁-b (cons '(≤ x 0) (↦ ['x 1])))
                (set     (cons '(≤ 1 0) (↦ ['x 1]))))
  (check-equal? (step₁-b (cons '(≤ x 3) (↦ ['x 2])))
                (set     (cons '(≤ 2 3) (↦ ['x 2]))))
  (check-equal? (step₁-b (cons '(¬ (≤ x 0)) (↦ ['x 1])))
                (set     (cons '(¬ (≤ 1 0)) (↦ ['x 1]))))
  (check-equal? (step₁-b (cons '(¬ (≤ x 3)) (↦ ['x 2])))
                (set     (cons '(¬ (≤ 2 3)) (↦ ['x 2]))))
  (check-equal? (step₁-b (cons '(∧ (≤ x 0) (≤ x 3)) (↦ ['x 1])))
                (set     (cons '(∧ (≤ 1 0) (≤ x 3)) (↦ ['x 1]))))
  (check-equal? (step₁-b (cons '(∧ (≤ x 2) (≤ x 3)) (↦ ['x 1])))
                (set     (cons '(∧ (≤ 1 2) (≤ x 3)) (↦ ['x 1]))))
  (check-equal? (step₁-b (cons '(∨ (≤ x -1) (≤ x 0)) (↦ ['x 1])))
                (set     (cons '(∨ (≤ 1 -1) (≤ x 0)) (↦ ['x 1]))))
  (check-equal? (step₁-b (cons '(∨ (≤ x 0) (≤ x 3)) (↦ ['x 1])))
                (set     (cons '(∨ (≤ 1 0) (≤ x 3)) (↦ ['x 1]))))
  (check-equal? (step₁-b (cons '(∨ (≤ x 2) (≤ x 3)) (↦ ['x 1])))
                (set     (cons '(∨ (≤ 1 2) (≤ x 3)) (↦ ['x 1]))))

  (check-equal? (car (-->>₁b (cons #t (↦))))
                (set         (cons #t (↦))))
  (check-equal? (car (-->>₁b (cons #f (↦))))
                (set         (cons #f (↦))))
  (check-equal? (car (-->>₁b (cons '(= x 1) (↦ ['x 1]))))
                (set         (cons #t       (↦ ['x 1]))))
  (check-equal? (car (-->>₁b (cons '(= x 1) (↦ ['x 2]))))
                (set         (cons #f       (↦ ['x 2]))))
  (check-equal? (car (-->>₁b (cons '(≤ x 0) (↦ ['x 1]))))
                (set         (cons #f       (↦ ['x 1]))))
  (check-equal? (car (-->>₁b (cons '(≤ x 3) (↦ ['x 2]))))
                (set         (cons #t       (↦ ['x 2]))))
  (check-equal? (car (-->>₁b (cons '(¬ (≤ x 0)) (↦ ['x 1]))))
                (set         (cons #t           (↦ ['x 1]))))
  (check-equal? (car (-->>₁b (cons '(¬ (≤ x 3)) (↦ ['x 2]))))
                (set         (cons #f           (↦ ['x 2]))))
  (check-equal? (car (-->>₁b (cons '(∧ (≤ x 0) (≤ x 3)) (↦ ['x 1]))))
                (set         (cons #f                   (↦ ['x 1]))))
  (check-equal? (car (-->>₁b (cons '(∧ (≤ x 2) (≤ x 3)) (↦ ['x 1]))))
                (set         (cons #t                   (↦ ['x 1]))))
  (check-equal? (car (-->>₁b (cons '(∨ (≤ x -1) (≤ x 0)) (↦ ['x 1]))))
                (set         (cons #f                    (↦ ['x 1]))))
  (check-equal? (car (-->>₁b (cons '(∨ (≤ x 0) (≤ x 3)) (↦ ['x 1]))))
                (set         (cons #t                   (↦ ['x 1]))))
  (check-equal? (car (-->>₁b (cons '(∨ (≤ x 2) (≤ x 3)) (↦ ['x 1]))))
                (set         (cons #t                   (↦ ['x 1])))))


(define-reduction (-->₁c -->₁a -->₁b)
  #:monad (StateT #f (NondetT ID))

  ['skip
   (void)]

  [`(≔ ,x ,a)
   a′ ← (-->₁a a)
   `(≔ ,x ,a′)]

  [`(≔ ,x ,(? number? m))
   σ ← get
   (put (σ x m))
   (void)]

  [`(seq ,c₀ ,c₁)
   c₀′ ← (-->₁c c₀) 
   `(seq ,c₀′ ,c₁)]

  [`(seq ,(? void?) ,c₁)
   c₁]

  [`(if ,b ,c₀ ,c₁)
   b′ ← (-->₁b b)
   `(if ,b′ ,c₀ ,c₁)]

  [`(if #t ,c₀ ,c₁)
   c₀]

  [`(if #f ,c₀ ,c₁)
   c₁]

  [`(while ,b ,c)
   `(if ,b
      (seq ,c (while ,b ,c))
      skip)])

(define (step₁-c cσ)
  (define reducer₁-a (reducer-of (-->₁a)))
  (define-values (mrun reducer)
    (-->₁c reducer₁-a (reducer-of (-->₁b reducer₁-a))))
  (match-define (cons c σ) cσ)
  (mrun σ (reducer c)))
(define -->>₁c (repeated step₁-c))

(define ((~₁c c₀ c₁) σ)
  (equal? (step₁-c c₀ σ) (step₁-c c₁ σ)))

(module+ test
  (check-equal? (step₁-c (cons 'skip  (↦ ['x 1])))
                (set     (cons (void) (↦ ['x 1]))))
  (check-equal? (step₁-c (cons '(≔ x (+ x 1)) (↦ ['x 1])))
                (set     (cons '(≔ x (+ 1 1)) (↦ ['x 1]))))
  (check-equal? (step₁-c (cons '(seq (≔ x (+ x 1)) (≔ y (+ y x)))
                               (↦ ['x 1] ['y 1])))
                (set     (cons '(seq (≔ x (+ 1 1)) (≔ y (+ y x)))
                               (↦ ['x 1] ['y 1]))))
  (check-equal? (step₁-c (cons '(if (≤ x 1)
                                  (≔ x (+ x 1))
                                  skip)
                               (↦ ['x 1])))
                (set     (cons '(if (≤ 1 1)
                                  (≔ x (+ x 1))
                                  skip)
                               (↦ ['x 1]))))
  (check-equal? (step₁-c (cons '(if (≤ x 1)
                                  (≔ x (+ x 1))
                                  skip)
                               (↦ ['x 2])))
                (set     (cons '(if (≤ 2 1)
                                  (≔ x (+ x 1))
                                  skip)
                               (↦ ['x 2]))))
  (check-equal? (step₁-c (cons '(while (¬ (= x 0))
                                  (seq (≔ sum (+ sum x))
                                       (≔ x (- x 1))))
                               (↦ ['x 10] ['sum 0])))
                (set     (cons '(if (¬ (= x 0))
                                  (seq
                                   (seq (≔ sum (+ sum x))
                                        (≔ x (- x 1)))
                                   (while (¬ (= x 0))
                                     (seq (≔ sum (+ sum x))
                                          (≔ x (- x 1)))))
                                  skip)
                               (↦ ['x 10] ['sum 0]))))

  (check-equal? (car (-->>₁c (cons 'skip  (↦ ['x 1]))))
                (set         (cons (void) (↦ ['x 1]))))
  (check-equal? (car (-->>₁c (cons '(≔ x (+ x 1)) (↦ ['x 1]))))
                (set         (cons (void)         (↦ ['x 2]))))
  (check-equal? (car (-->>₁c (cons '(seq (≔ x (+ x 1)) (≔ y (+ y x)))
                                   (↦ ['x 1] ['y 1]))))
                (set (cons (void)  (↦ ['x 2] ['y 3]))))
  (check-equal? (car (-->>₁c (cons '(if (≤ x 1)
                                      (≔ x (+ x 1))
                                      skip)
                                   (↦ ['x 1]))))
                (set (cons (void)  (↦ ['x 2]))))
  (check-equal? (car (-->>₁c (cons '(if (≤ x 1)
                                      (≔ x (+ x 1))
                                      skip)
                                   (↦ ['x 2]))))
                (set (cons (void)  (↦ ['x 2]))))
  (check-equal? (car (-->>₁c (cons '(while (¬ (= x 0))
                                      (seq (≔ sum (+ sum x))
                                           (≔ x (- x 1))))
                                   (↦ ['x 10] ['sum  0]))))
                (set (cons (void)  (↦ ['x  0] ['sum 55])))))

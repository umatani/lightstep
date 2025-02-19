#lang racket
(require lightstep/base
         (only-in lightstep/transformers
                  with-monad run-StateT StateT NondetT ID))

(module+ test (require rackunit))

;;=============================================================================
;; 2.2 The evaluation of arithmetic expressions

(define-reduction (-->a-rules -->a)
  #:monad (StateT #f (NondetT ID))
  #:mrun (λ (m) (run-StateT (↦) m))

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

(define-values (mrun-a reducer-a)
  (invoke-unit (inst-reduction -->a-rules reducer-a)))
(define (-->a a [σ (↦)])
  (mrun-a (with-monad (StateT #f (NondetT ID))
            (do (put σ)
                (reducer-a a)))))

(define ((~a a₀ a₁) σ)
  (equal? (-->a a₀ σ) (-->a a₁ σ)))

(module+ test
  (define σ (↦ ['x 3] ['y 2]))
  (check-equal? (-->a 3) (set (cons 3 (↦))))
  (check-equal? (-->a 'y σ) (set (cons 2 σ)))
  (check-equal? (-->a '(+ x 1) σ) (set (cons 4 σ)))
  (check-equal? (-->a '(+ x y) σ) (set (cons 5 σ)))
  (check-equal? (-->a '(- x y) σ) (set (cons 1 σ)))
  (check-equal? (-->a '(× x y) σ) (set (cons 6 σ)))

  (check-equal? (-->a '(+ (+ Init 5) (+ 7 9)) (↦ ['Init 0]))
                (set (cons 21 (↦ ['Init 0])))))

;;=============================================================================
;; 2.3 The evaluation of boolean expressions

(define-reduction (-->b-rules -->a -->b)
  #:monad (StateT #f (NondetT ID))
  #:mrun (λ (m) (run-StateT (↦) m))

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

(define-values (mrun-b reducer-b)
  (invoke-unit (inst-reduction -->b-rules reducer-a reducer-b)))
(define (-->b b [σ (↦)])
  (mrun-b (with-monad (StateT #f (NondetT ID))
            (do (put σ)
                (reducer-b b)))))

(define ((~b b₀ b₁) σ)
  (equal? (-->b b₀ σ) (-->b b₁ σ)))

(module+ test
  (check-equal? (-->b #t) (set (cons #t (↦))))
  (check-equal? (-->b #f) (set (cons #f (↦))))
  (check-equal? (-->b '(= x 1) (↦ ['x 1])) (set (cons #t (↦ ['x 1]))))
  (check-equal? (-->b '(= x 1) (↦ ['x 2])) (set (cons #f (↦ ['x 2]))))
  (check-equal? (-->b '(≤ x 0) (↦ ['x 1])) (set (cons #f (↦ ['x 1]))))
  (check-equal? (-->b '(≤ x 3) (↦ ['x 2])) (set (cons #t (↦ ['x 2]))))
  (check-equal? (-->b '(¬ (≤ x 0)) (↦ ['x 1])) (set (cons #t (↦ ['x 1]))))
  (check-equal? (-->b '(¬ (≤ x 3)) (↦ ['x 2])) (set (cons #f (↦ ['x 2]))))
  (check-equal? (-->b '(∧ (≤ x 0) (≤ x 3)) (↦ ['x 1]))
                (set (cons #f (↦ ['x 1]))))
  (check-equal? (-->b '(∧ (≤ x 2) (≤ x 3)) (↦ ['x 1]))
                (set (cons #t (↦ ['x 1]))))
  (check-equal? (-->b '(∨ (≤ x -1) (≤ x 0)) (↦ ['x 1]))
                (set (cons #f (↦ ['x 1]))))
  (check-equal? (-->b '(∨ (≤ x 0) (≤ x 3)) (↦ ['x 1]))
                (set (cons #t (↦ ['x 1]))))
  (check-equal? (-->b '(∨ (≤ x 2) (≤ x 3)) (↦ ['x 1]))
                (set (cons #t (↦ ['x 1])))))

(module+ left-first-sequential
  (require rackunit)

  (define-reduction (-->b′-rules -->a -->b′) #:super (-->b-rules -->a -->b′)
    #:monad (StateT #f (NondetT ID))
    #:mrun (λ (m) (run-StateT (↦) m))

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

  (define-values (mrun-b′ reducer-b′)
    (invoke-unit (inst-reduction -->b′-rules reducer-a reducer-b′)))
  (define (-->b′ b [σ (↦)])
    (mrun-b′ (with-monad (StateT #f (NondetT ID))
               (do (put σ)
                   (reducer-b′ b)))))

  (check-equal? (-->b′ #t) (set (cons #t (↦))))
  (check-equal? (-->b′ #f) (set (cons #f (↦))))
  (check-equal? (-->b′ '(= x 1) (↦ ['x 1])) (set (cons #t (↦ ['x 1]))))
  (check-equal? (-->b′ '(= x 1) (↦ ['x 2])) (set (cons #f (↦ ['x 2]))))
  (check-equal? (-->b′ '(≤ x 0) (↦ ['x 1])) (set (cons #f (↦ ['x 1]))))
  (check-equal? (-->b′ '(≤ x 3) (↦ ['x 2])) (set (cons #t (↦ ['x 2]))))
  (check-equal? (-->b′ '(¬ (≤ x 0)) (↦ ['x 1])) (set (cons #t (↦ ['x 1]))))
  (check-equal? (-->b′ '(¬ (≤ x 3)) (↦ ['x 2])) (set (cons #f (↦ ['x 2]))))
  (check-equal? (-->b′ '(∧ (≤ x 0) (≤ x 3)) (↦ ['x 1]))
                (set (cons #f (↦ ['x 1]))))
  (check-equal? (-->b′ '(∧ (≤ x 2) (≤ x 3)) (↦ ['x 1]))
                (set (cons #t (↦ ['x 1]))))
  (check-equal? (-->b′ '(∨ (≤ x -1) (≤ x 0)) (↦ ['x 1]))
                (set (cons #f (↦ ['x 1]))))
  (check-equal? (-->b′ '(∨ (≤ x 0) (≤ x 3)) (↦ ['x 1]))
                (set (cons #t (↦ ['x 1]))))
  (check-equal? (-->b′ '(∨ (≤ x 2) (≤ x 3)) (↦ ['x 1]))
                (set (cons #t (↦ ['x 1])))))

(module+ parallel-or
  (require rackunit)

  (define-reduction (-->b′-rules -->a -->b′) #:super (-->b-rules -->a -->b′)
    #:monad (StateT #f (NondetT ID))
    #:mrun (λ (m) (run-StateT (↦) m))

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

  (define-values (mrun-b′ reducer-b′)
    (invoke-unit (inst-reduction -->b′-rules reducer-a reducer-b′)))
  (define (-->b′ b [σ (↦)])
    (mrun-b′ (with-monad (StateT #f (NondetT ID))
               (do (put σ)
                   (reducer-b′ b)))))

  (check-equal? (-->b′ #t) (set (cons #t (↦))))
  (check-equal? (-->b′ #f) (set (cons #f (↦))))
  (check-equal? (-->b′ '(= x 1) (↦ ['x 1])) (set (cons #t (↦ ['x 1]))))
  (check-equal? (-->b′ '(= x 1) (↦ ['x 2])) (set (cons #f (↦ ['x 2]))))
  (check-equal? (-->b′ '(≤ x 0) (↦ ['x 1])) (set (cons #f (↦ ['x 1]))))
  (check-equal? (-->b′ '(≤ x 3) (↦ ['x 2])) (set (cons #t (↦ ['x 2]))))
  (check-equal? (-->b′ '(¬ (≤ x 0)) (↦ ['x 1])) (set (cons #t (↦ ['x 1]))))
  (check-equal? (-->b′ '(¬ (≤ x 3)) (↦ ['x 2])) (set (cons #f (↦ ['x 2]))))
  (check-equal? (-->b′ '(∧ (≤ x 0) (≤ x 3)) (↦ ['x 1]))
                (set (cons #f (↦ ['x 1]))))
  (check-equal? (-->b′ '(∧ (≤ x 2) (≤ x 3)) (↦ ['x 1]))
                (set (cons #t (↦ ['x 1]))))
  (check-equal? (-->b′ '(∨ (≤ x -1) (≤ x 0)) (↦ ['x 1]))
                (set (cons #f (↦ ['x 1]))))
  (check-equal? (-->b′ '(∨ (≤ x 0) (≤ x 3)) (↦ ['x 1]))
                (set (cons #t (↦ ['x 1]))))
  (check-equal? (-->b′ '(∨ (≤ x 2) (≤ x 3)) (↦ ['x 1]))
                (set (cons #t (↦ ['x 1])))))


;;=============================================================================
;; 2.4 The execution of commands

(define-reduction (-->c-rules -->a -->b -->c)
  #:monad (StateT #f (NondetT ID))
  #:mrun (λ (m) (run-StateT (↦) m))

  ['skip
   (void)
   "skip"]

  [`(≔ ,X ,a)
   m ← (-->a a)
   σ ← get
   (put (σ X m))
   (void)
   "assign"]

  [`(seq ,c₀ ,c₁)
   (-->c c₀) 
   (-->c c₁)
   (void)
   "seq"]

  [`(if ,b ,c₀ ,c₁)
   #t ← (-->b b)
   (-->c c₀)
   (void)
   "if-t"]

  [`(if ,b ,c₀ ,c₁)
   #f ← (-->b b)
   (-->c c₁)
   (void)
   "if-f"]

  [`(while ,b ,c)
   #f ← (-->b b)
   (void)
   "while-f"]

  [`(while ,b ,c)
   #t ← (-->b b)
   (-->c c)
   (-->c `(while ,b ,c))
   (void)
   "while-t"])

(define-values (mrun-c reducer-c)
  (invoke-unit (inst-reduction -->c-rules reducer-a reducer-b reducer-c)))
(define (-->c c [σ (↦)])
  (mrun-c (with-monad (StateT #f (NondetT ID))
            (do (put σ)
                (reducer-c c)))))

(define ((~c c₀ c₁) σ)
  (equal? (-->c c₀ σ) (-->c c₁ σ)))

(module+ test
  (check-equal? (-->c 'skip (↦ ['x 1]))
                (set (cons (void) (↦ ['x 1]))))
  (check-equal? (-->c '(≔ x (+ x 1)) (↦ ['x 1]))
                (set (cons (void) (↦ ['x 2]))))
  (check-equal? (-->c '(seq (≔ x (+ x 1)) (≔ y (+ y x))) (↦ ['x 1] ['y 1]))
                (set (cons (void) (↦ ['x 2] ['y 3]))))
  (check-equal? (-->c '(if (≤ x 1)
                         (≔ x (+ x 1))
                         skip)
                      (↦ ['x 1]))
                (set (cons (void) (↦ ['x 2]))))
  (check-equal? (-->c '(if (≤ x 1)
                         (≔ x (+ x 1))
                         skip)
                      (↦ ['x 1]))
                (set (cons (void) (↦ ['x 2]))))
  (check-equal? (-->c '(if (≤ x 1)
                         (≔ x (+ x 1))
                         skip)
                      (↦ ['x 0]))
                (set (cons (void) (↦ ['x 1]))))
  (check-equal? (-->c '(while (¬ (= x 0))
                         (seq (≔ sum (+ sum x))
                              (≔ x (- x 1))))
                      (↦ ['x 10] ['sum 0]))
                (set (cons (void) (↦ ['x 0] ['sum 55])))))

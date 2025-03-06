#lang racket/base
(require lightstep/base)

(module+ test (require rackunit))

;;=============================================================================
;; 2.2 The evaluation of arithmetic expressions

(define-reduction (-->a)
  [`(,(? number? n) ,σ)
   n
   "number"]

  [`(,(? symbol? X) ,σ)
   (σ X)
   "location"]

  [`((+ ,a₀ ,a₁) ,σ)
   n₀ ← (-->a `(,a₀ ,σ))
   n₁ ← (-->a `(,a₁ ,σ))
   (+ n₀ n₁)
   "sum"]

  [`((- ,a₀ ,a₁) ,σ)
   n₀ ← (-->a `(,a₀ ,σ))
   n₁ ← (-->a `(,a₁ ,σ))
   (- n₀ n₁)
   "subtract"]

  [`((× ,a₀ ,a₁) ,σ)
   n₀ ← (-->a `(,a₀ ,σ))
   n₁ ← (-->a `(,a₁ ,σ))
   (* n₀ n₁)
   "product"])

(define step-a (call-with-values (λ () (-->a)) compose1))

(define ((~a a₀ a₁) σ)
  (equal? (step-a `(,a₀ ,σ)) (step-a `(,a₁ ,σ))))

(module+ test
  (check-equal? (step-a `(3 ,(↦))) (set 3))
  (check-equal? (step-a `(y ,(↦ ['x 3] ['y 2]))) (set 2))
  (check-equal? (step-a `((+ x 1) ,(↦ ['x 3] ['y 2]))) (set 4))
  (check-equal? (step-a `((+ x y) ,(↦ ['x 3] ['y 2]))) (set 5))
  (check-equal? (step-a `((- x y) ,(↦ ['x 3] ['y 2]))) (set 1))
  (check-equal? (step-a `((× x y) ,(↦ ['x 3] ['y 2]))) (set 6))

  (check-equal? (step-a `((+ (+ Init 5) (+ 7 9)) ,(↦ ['Init 0]))) (set 21)))

;;=============================================================================
;; 2.3 The evaluation of boolean expressions

(define-reduction (-->b -->a)
  [`(#t ,σ)
   #t
   "true"]

  [`(#f ,σ)
   #f
   "false"]

  [`((= ,a₀ ,a₁) ,σ)
   n ← (-->a `(,a₀ ,σ))
   m ← (-->a `(,a₁ ,σ))
   #:when (= n m)
   #t
   "equal"]

  [`((= ,a₀ ,a₁) ,σ)
   n ← (-->a `(,a₀ ,σ))
   m ← (-->a `(,a₁ ,σ))
   #:unless (= n m)
   #f
   "not equal"]

  [`((≤ ,a₀ ,a₁) ,σ)
   n ← (-->a `(,a₀ ,σ))
   m ← (-->a `(,a₁ ,σ))
   #:when (<= n m)
   #t
   "less than or equal"]

  [`((≤ ,a₀ ,a₁) ,σ)
   n ← (-->a `(,a₀ ,σ))
   m ← (-->a `(,a₁ ,σ))
   #:unless (<= n m)
   #f
   "not less than or equal"]

  [`((¬ ,b) ,σ)
   #t ← (-->b `(,b ,σ))
   #f
   "not-true"]

  [`((¬ ,b) ,σ)
   #f ← (-->b `(,b ,σ))
   #t
   "not-false"]

  [`((∧ ,b₀ ,b₁) ,σ)
   t₀ ← (-->b `(,b₀ ,σ))
   t₁ ← (-->b `(,b₁ ,σ))
   (and t₀ t₁)
   "and"]

  [`((∨ ,b₀ ,b₁) ,σ)
   t₀ ← (-->b `(,b₀ ,σ))
   t₁ ← (-->b `(,b₁ ,σ))
   (or t₀ t₁)
   "or"])

(define step-b (call-with-values (λ () (-->b (reducer-of (-->a)))) compose1))

(define ((~b b₀ b₁) σ)
  (equal? (step-b `(,b₀ ,σ)) (step-b `(,b₁ ,σ))))

(module+ test
  (check-equal? (step-b `(#t ,(↦))) (set #t))
  (check-equal? (step-b `(#f ,(↦))) (set #f))
  (check-equal? (step-b `((= x 1) ,(↦ ['x 1]))) (set #t))
  (check-equal? (step-b `((= x 1) ,(↦ ['x 2]))) (set #f))
  (check-equal? (step-b `((≤ x 0) ,(↦ ['x 1]))) (set #f))
  (check-equal? (step-b `((≤ x 3) ,(↦ ['x 2]))) (set #t))
  (check-equal? (step-b `((¬ (≤ x 0)) ,(↦ ['x 1]))) (set #t))
  (check-equal? (step-b `((¬ (≤ x 3)) ,(↦ ['x 2]))) (set #f))
  (check-equal? (step-b `((∧ (≤ x 0) (≤ x 3)) ,(↦ ['x 1]))) (set #f))
  (check-equal? (step-b `((∧ (≤ x 2) (≤ x 3)) ,(↦ ['x 1]))) (set #t))
  (check-equal? (step-b `((∨ (≤ x -1) (≤ x 0)) ,(↦ ['x 1]))) (set #f))
  (check-equal? (step-b `((∨ (≤ x 0) (≤ x 3)) ,(↦ ['x 1]))) (set #t))
  (check-equal? (step-b `((∨ (≤ x 2) (≤ x 3)) ,(↦ ['x 1]))) (set #t)))

(module+ left-first-sequential
  (require rackunit)

  (define-reduction (-->b′ -->a) #:super [(-->b -->a)]
    ;; remove super's "and" rule
    [`((∧ ,b₀ ,b₁) ,σ)
     #:when #f
     (void)
     "and"]

    [`((∧ ,b₀ ,b₁) ,σ)
     #f ← (-->b′ `(,b₀ ,σ))
     #f
     "and-f"]

    [`((∧ ,b₀ ,b₁) ,σ)
     #t ← (-->b′ `(,b₀ ,σ))
     #f ← (-->b′ `(,b₁ ,σ))
     #f
     "and-tf"]

    [`((∧ ,b₀ ,b₁) ,σ)
     #t ← (-->b′ `(,b₀ ,σ))
     #t ← (-->b′ `(,b₁ ,σ))
     #t
     "and-tt"]

    ;; remove super's "or" rule
    [`((∨ ,b₀ ,b₁) ,σ)
     #:when #f
     (void)
     "or"]

    [`((∨ ,b₀ ,b₁) ,σ)
     #t ← (-->b′ `(,b₀ ,σ))
     #t
     "or-t"]

    [`((∨ ,b₀ ,b₁) ,σ)
     #f ← (-->b′ `(,b₀ ,σ))
     #t ← (-->b′ `(,b₁ ,σ))
     #t
     "or-ft"]

    [`((∨ ,b₀ ,b₁) ,σ)
     #f ← (-->b′ `(,b₀ ,σ))
     #f ← (-->b′ `(,b₁ ,σ))
     #f
     "or-ff"])

  (define step-b′ (call-with-values
                   (λ () (-->b′ (reducer-of (-->a))))
                   compose1))

  (check-equal? (step-b′ `(#t ,(↦))) (set #t))
  (check-equal? (step-b′ `(#f ,(↦))) (set #f))
  (check-equal? (step-b′ `((= x 1) ,(↦ ['x 1]))) (set #t))
  (check-equal? (step-b′ `((= x 1) ,(↦ ['x 2]))) (set #f))
  (check-equal? (step-b′ `((≤ x 0) ,(↦ ['x 1]))) (set #f))
  (check-equal? (step-b′ `((≤ x 3) ,(↦ ['x 2]))) (set #t))
  (check-equal? (step-b′ `((¬ (≤ x 0)) ,(↦ ['x 1]))) (set #t))
  (check-equal? (step-b′ `((¬ (≤ x 3)) ,(↦ ['x 2]))) (set #f))
  (check-equal? (step-b′ `((∧ (≤ x 0) (≤ x 3)) ,(↦ ['x 1]))) (set #f))
  (check-equal? (step-b′ `((∧ (≤ x 2) (≤ x 3)) ,(↦ ['x 1]))) (set #t))
  (check-equal? (step-b′ `((∨ (≤ x -1) (≤ x 0)) ,(↦ ['x 1]))) (set #f))
  (check-equal? (step-b′ `((∨ (≤ x 0) (≤ x 3)) ,(↦ ['x 1]))) (set #t))
  (check-equal? (step-b′ `((∨ (≤ x 2) (≤ x 3)) ,(↦ ['x 1]))) (set #t)))

(module+ parallel-or
  (require rackunit)

  (define-reduction (-->b′ -->a) #:super [(-->b -->a)]
    ;; remove super's "or" rule
    [`((∨ ,b₀ ,b₁) ,σ)
     #:when #f
     (void)
     "or"]

    [`((∨ ,b₀ ,b₁) ,σ)
     #t ← (-->b′ `(,b₀ ,σ))
     #t
     "or-l"]

    [`((∨ ,b₀ ,b₁) ,σ)
     #t ← (-->b′ `(,b₁ ,σ))
     #t
     "or-r"]

    [`((∨ ,b₀ ,b₁) ,σ)
     #f ← (-->b′ `(,b₀ ,σ))
     #f ← (-->b′ `(,b₁ ,σ))
     #f
     "or-ff"])

  (define step-b′ (call-with-values
                   (λ () (-->b′ (reducer-of (-->a))))
                   compose1))

  (check-equal? (step-b′ `(#t ,(↦))) (set #t))
  (check-equal? (step-b′ `(#f ,(↦))) (set #f))
  (check-equal? (step-b′ `((= x 1) ,(↦ ['x 1]))) (set #t))
  (check-equal? (step-b′ `((= x 1) ,(↦ ['x 2]))) (set #f))
  (check-equal? (step-b′ `((≤ x 0) ,(↦ ['x 1]))) (set #f))
  (check-equal? (step-b′ `((≤ x 3) ,(↦ ['x 2]))) (set #t))
  (check-equal? (step-b′ `((¬ (≤ x 0)) ,(↦ ['x 1]))) (set #t))
  (check-equal? (step-b′ `((¬ (≤ x 3)) ,(↦ ['x 2]))) (set #f))
  (check-equal? (step-b′ `((∧ (≤ x 0) (≤ x 3)) ,(↦ ['x 1]))) (set #f))
  (check-equal? (step-b′ `((∧ (≤ x 2) (≤ x 3)) ,(↦ ['x 1]))) (set #t))
  (check-equal? (step-b′ `((∨ (≤ x -1) (≤ x 0)) ,(↦ ['x 1]))) (set #f))
  (check-equal? (step-b′ `((∨ (≤ x 0) (≤ x 3)) ,(↦ ['x 1]))) (set #t))
  (check-equal? (step-b′ `((∨ (≤ x 2) (≤ x 3)) ,(↦ ['x 1]))) (set #t)))


;;=============================================================================
;; 2.4 The execution of commands

(define-reduction (-->c -->a -->b)
  [`(skip ,σ)
   σ
   "skip"]

  [`((≔ ,x ,a) ,σ)
   m ← (-->a `(,a ,σ))
   (σ x m)
   "assign"]

  [`((seq ,c₀ ,c₁) ,σ)
   σ″ ← (-->c `(,c₀ ,σ))
   σ′ ← (-->c `(,c₁ ,σ″))
   σ′
   "seq"]

  [`((if ,b ,c₀ ,c₁) ,σ)
   #t ← (-->b `(,b ,σ))
   σ′ ← (-->c `(,c₀ ,σ))
   σ′
   "if-t"]

  [`((if ,b ,c₀ ,c₁) ,σ)
   #f ← (-->b `(,b ,σ))
   σ′ ← (-->c `(,c₁ ,σ))
   σ′
   "if-f"]

  [`((while ,b ,c) ,σ)
   #f ← (-->b `(,b ,σ))
   σ
   "while-f"]

  [`((while ,b ,c) ,σ)
   #t ← (-->b `(,b ,σ))
   σ″ ← (-->c `(,c ,σ))
   σ′ ← (-->c `((while ,b ,c) ,σ″))
   σ′
   "while-t"])

(define step-c (let ([reducer-a (reducer-of (-->a))])
                 (call-with-values
                  (λ () (-->c reducer-a (reducer-of (-->b reducer-a))))
                  compose1)))

(define ((~c c₀ c₁) σ)
  (equal? (step-c `(,c₀ ,σ)) (step-c `(,c₁ ,σ))))

(module+ test
  (check-equal? (step-c `(skip ,(↦ ['x 1]))) (set (↦ ['x 1])))
  (check-equal? (step-c `((≔ x (+ x 1)) ,(↦ ['x 1]))) (set (↦ ['x 2])))
  (check-equal? (step-c `((seq (≔ x (+ x 1)) (≔ y (+ y x))) ,(↦ ['x 1] ['y 1])))
                (set (↦ ['x 2] ['y 3])))
  (check-equal? (step-c `((if (≤ x 1)
                          (≔ x (+ x 1))
                          skip) ,(↦ ['x 1])))
                (set (↦ ['x 2])))
  (check-equal? (step-c `((if (≤ x 1)
                          (≔ x (+ x 1))
                          skip) ,(↦ ['x 2])))
                (set (↦ ['x 2])))
  (check-equal? (step-c `((while (¬ (= x 0))
                          (seq (≔ sum (+ sum x))
                               (≔ x (- x 1))))
                        ,(↦ ['x 10] ['sum 0])))
                (set (↦ ['x 0] ['sum 55]))))


;;=============================================================================
;; 2.6 Alternative semantics

(define-reduction (-->₁a)
  [`(,(? symbol? X) ,σ)
   `(,(σ X) ,σ)]

  [`((+ ,a₀ ,a₁) ,σ)
   `(,a₀′ ,(? (λ (σ′) (equal? σ σ′)))) ← (-->₁a `(,a₀ ,σ))
   `((+ ,a₀′ ,a₁) ,σ)]

  [`((+ ,(? number? n) ,a₁) ,σ)
   `(,a₁′ ,(? (λ (σ′) (equal? σ σ′)))) ← (-->₁a `(,a₁ ,σ))
   `((+ ,n ,a₁′) ,σ)]

  [`((+ ,(? number? n) ,(? number? m)) ,σ)
   p ≔ (+ n m)
   `(,p ,σ)]

  [`((- ,a₀ ,a₁) ,σ)
   `(,a₀′ ,(? (λ (σ′) (equal? σ σ′)))) ← (-->₁a `(,a₀ ,σ))
   `((- ,a₀′ ,a₁) ,σ)]

  [`((- ,(? number? n) ,a₁) ,σ)
   `(,a₁′ ,(? (λ (σ′) (equal? σ σ′)))) ← (-->₁a `(,a₁ ,σ))
   `((- ,n ,a₁′) ,σ)]

  [`((- ,(? number? n) ,(? number? m)) ,σ)
   p ≔ (- n m)
   `(,p ,σ)]

  [`((× ,a₀ ,a₁) ,σ)
   `(,a₀′ ,(? (λ (σ′) (equal? σ σ′)))) ← (-->₁a `(,a₀ ,σ))
   `((× ,a₀′ ,a₁) ,σ)]

  [`((× ,(? number? n) ,a₁) ,σ)
   `(,a₁′ ,(? (λ (σ′) (equal? σ σ′)))) ← (-->₁a `(,a₁ ,σ))
   `((× ,n ,a₁′) ,σ)]

  [`((× ,(? number? n) ,(? number? m)) ,σ)
   p ≔ (* n m)
   `(,p ,σ)])

(define step₁-a (call-with-values (λ () (-->₁a)) compose1))
(define -->>₁a (repeated step₁-a))

(define ((~₁a a₀ a₁) σ)
  (equal? (step₁-a `(,a₀ ,σ)) (step₁-a `(,a₁ ,σ))))

(module+ test
  (check-equal? (step₁-a `(3 ,(↦))) ∅)
  (check-equal? (step₁-a `(y ,(↦ ['x 3] ['y 2])))
                (set     `(2 ,(↦ ['x 3] ['y 2]))))
  (check-equal? (step₁-a `((+ x 1) ,(↦ ['x 3] ['y 2])))
                (set     `((+ 3 1) ,(↦ ['x 3] ['y 2]))))
  (check-equal? (step₁-a `((+ x y) ,(↦ ['x 3] ['y 2])))
                (set     `((+ 3 y) ,(↦ ['x 3] ['y 2]))))
  (check-equal? (step₁-a `((- x y) ,(↦ ['x 3] ['y 2])))
                (set     `((- 3 y) ,(↦ ['x 3] ['y 2]))))
  (check-equal? (step₁-a `((× x y) ,(↦ ['x 3] ['y 2])))
                (set     `((× 3 y) ,(↦ ['x 3] ['y 2]))))
  (check-equal? (step₁-a `((+ (+ Init 5) (+ 7 9)) ,(↦ ['Init 0])))
                (set     `((+ (+ 0 5) (+ 7 9))    ,(↦ ['Init 0]))))

  (check-equal? (car (-->>₁a `(3 ,(↦))))
                (set         `(3 ,(↦))))
  (check-equal? (car (-->>₁a `(y ,(↦ ['x 3] ['y 2]))))
                (set         `(2 ,(↦ ['x 3] ['y 2]))))
  (check-equal? (car (-->>₁a `((+ x 1) ,(↦ ['x 3] ['y 2]))))
                (set         `(4       ,(↦ ['x 3] ['y 2]))))
  (check-equal? (car (-->>₁a `((+ x y) ,(↦ ['x 3] ['y 2]))))
                (set         `(5       ,(↦ ['x 3] ['y 2]))))
  (check-equal? (car (-->>₁a `((- x y) ,(↦ ['x 3] ['y 2]))))
                (set         `(1       ,(↦ ['x 3] ['y 2]))))
  (check-equal? (car (-->>₁a `((× x y) ,(↦ ['x 3] ['y 2]))))
                (set         `(6       ,(↦ ['x 3] ['y 2]))))
  (check-equal? (car (-->>₁a `((+ (+ Init 5) (+ 7 9)) ,(↦ ['Init 0]))))
                (set         `(21                     ,(↦ ['Init 0])))))


(define-reduction (-->₁b -->₁a)
  [`((= ,a₀ ,a₁) ,σ)
   `(,a₀′ ,(? (λ (σ′) (equal? σ σ′)))) ← (-->₁a `(,a₀ ,σ))
   `((= ,a₀′ ,a₁) ,σ)]

  [`((= ,(? number? n) ,a₁) ,σ)
   `(,a₁′ ,(? (λ (σ′) (equal? σ σ′)))) ← (-->₁a `(,a₁ ,σ))
   `((= ,n ,a₁′) ,σ)]

  [`((= ,(? number? n) ,(? number? m)) ,σ)
   #:when (= n m)
   `(#t ,σ)]

  [`((= ,(? number? n) ,(? number? m)) ,σ)
   #:unless (= n m)
   `(#f ,σ)]

  [`((≤ ,a₀ ,a₁) ,σ)
   `(,a₀′ ,(? (λ (σ′) (equal? σ σ′)))) ← (-->₁a `(,a₀ ,σ))
   `((≤ ,a₀′ ,a₁) ,σ)]

  [`((≤ ,(? number? n) ,a₁) ,σ)
   `(,a₁′ ,(? (λ (σ′) (equal? σ σ′)))) ← (-->₁a `(,a₁ ,σ))
   `((≤ ,n ,a₁′) ,σ)]

  [`((≤ ,(? number? n) ,(? number? m)) ,σ)
   #:when (<= n m)
   `(#t ,σ)]

  [`((≤ ,(? number? n) ,(? number? m)) ,σ)
   #:unless (<= n m)
   `(#f ,σ)]

  [`((¬ ,b) ,σ)
   `(,b′ ,(? (λ (σ′) (equal? σ σ′)))) ← (-->₁b `(,b ,σ))
   `((¬ ,b′) ,σ)]

  [`((¬ #t) ,σ)
   `(#f ,σ)]

  [`((¬ #f) ,σ)
   `(#t ,σ)]

  [`((∧ ,b₀ ,b₁) ,σ)
   `(,b₀′ ,(? (λ (σ′) (equal? σ σ′)))) ← (-->₁b `(,b₀ ,σ))
   `((∧ ,b₀′ ,b₁) ,σ)]

  [`((∧ ,(? boolean? t₀) ,b₁) ,σ)
   `(,b₁′ ,(? (λ (σ′) (equal? σ σ′)))) ← (-->₁b `(,b₁ ,σ))
   `((∧ ,t₀ ,b₁′) ,σ)]

  [`((∧ ,(? boolean? t₀) ,(? boolean? t₁)) ,σ)
   `(,(and t₀ t₁) ,σ)]

  [`((∨ ,b₀ ,b₁) ,σ)
   `(,b₀′ ,(? (λ (σ′) (equal? σ σ′)))) ← (-->₁b `(,b₀ ,σ))
   `((∨ ,b₀′ ,b₁) ,σ)]

  [`((∨ ,(? boolean? t₀) ,b₁) ,σ)
   `(,b₁′ ,(? (λ (σ′) (equal? σ σ′)))) ← (-->₁b `(,b₁ ,σ))
   `((∨ ,t₀ ,b₁′) ,σ)]

  [`((∨ ,(? boolean? t₀) ,(? boolean? t₁)) ,σ)
   `(,(or t₀ t₁) ,σ)])

(define step₁-b (call-with-values (λ () (-->₁b (reducer-of (-->₁a)))) compose1))
(define -->>₁b (repeated step₁-b))

(define ((~b₁ b₀ b₁) σ)
  (equal? (step₁-b `(,b₀ ,σ)) (step₁-b `(,b₁ ,σ))))

(module+ test
  (check-equal? (step₁-b `(#t ,(↦))) ∅)
  (check-equal? (step₁-b `(#f ,(↦))) ∅)
  (check-equal? (step₁-b `((= x 1) ,(↦ ['x 1])))
                (set     `((= 1 1) ,(↦ ['x 1]))))
  (check-equal? (step₁-b `((= x 1) ,(↦ ['x 2])))
                (set     `((= 2 1) ,(↦ ['x 2]))))
  (check-equal? (step₁-b `((≤ x 0) ,(↦ ['x 1])))
                (set     `((≤ 1 0) ,(↦ ['x 1]))))
  (check-equal? (step₁-b `((≤ x 3) ,(↦ ['x 2])))
                (set     `((≤ 2 3) ,(↦ ['x 2]))))
  (check-equal? (step₁-b `((¬ (≤ x 0)) ,(↦ ['x 1])))
                (set     `((¬ (≤ 1 0)) ,(↦ ['x 1]))))
  (check-equal? (step₁-b `((¬ (≤ x 3)) ,(↦ ['x 2])))
                (set     `((¬ (≤ 2 3)) ,(↦ ['x 2]))))
  (check-equal? (step₁-b `((∧ (≤ x 0) (≤ x 3)) ,(↦ ['x 1])))
                (set     `((∧ (≤ 1 0) (≤ x 3)) ,(↦ ['x 1]))))
  (check-equal? (step₁-b `((∧ (≤ x 2) (≤ x 3)) ,(↦ ['x 1])))
                (set     `((∧ (≤ 1 2) (≤ x 3)) ,(↦ ['x 1]))))
  (check-equal? (step₁-b `((∨ (≤ x -1) (≤ x 0)) ,(↦ ['x 1])))
                (set     `((∨ (≤ 1 -1) (≤ x 0)) ,(↦ ['x 1]))))
  (check-equal? (step₁-b `((∨ (≤ x 0) (≤ x 3)) ,(↦ ['x 1])))
                (set     `((∨ (≤ 1 0) (≤ x 3)) ,(↦ ['x 1]))))
  (check-equal? (step₁-b `((∨ (≤ x 2) (≤ x 3)) ,(↦ ['x 1])))
                (set     `((∨ (≤ 1 2) (≤ x 3)) ,(↦ ['x 1]))))

  (check-equal? (car (-->>₁b `(#t ,(↦))))
                (set         `(#t ,(↦))))
  (check-equal? (car (-->>₁b `(#f ,(↦))))
                (set         `(#f ,(↦))))
  (check-equal? (car (-->>₁b `((= x 1) ,(↦ ['x 1]))))
                (set         `(#t      ,(↦ ['x 1]))))
  (check-equal? (car (-->>₁b `((= x 1) ,(↦ ['x 2]))))
                (set         `(#f      ,(↦ ['x 2]))))
  (check-equal? (car (-->>₁b `((≤ x 0) ,(↦ ['x 1]))))
                (set         `(#f      ,(↦ ['x 1]))))
  (check-equal? (car (-->>₁b `((≤ x 3) ,(↦ ['x 2]))))
                (set         `(#t      ,(↦ ['x 2]))))
  (check-equal? (car (-->>₁b `((¬ (≤ x 0)) ,(↦ ['x 1]))))
                (set         `(#t          ,(↦ ['x 1]))))
  (check-equal? (car (-->>₁b `((¬ (≤ x 3)) ,(↦ ['x 2]))))
                (set         `(#f          ,(↦ ['x 2]))))
  (check-equal? (car (-->>₁b `((∧ (≤ x 0) (≤ x 3)) ,(↦ ['x 1]))))
                (set         `(#f                  ,(↦ ['x 1]))))
  (check-equal? (car (-->>₁b `((∧ (≤ x 2) (≤ x 3)) ,(↦ ['x 1]))))
                (set         `(#t                  ,(↦ ['x 1]))))
  (check-equal? (car (-->>₁b `((∨ (≤ x -1) (≤ x 0)) ,(↦ ['x 1]))))
                (set         `(#f                   ,(↦ ['x 1]))))
  (check-equal? (car (-->>₁b `((∨ (≤ x 0) (≤ x 3)) ,(↦ ['x 1]))))
                (set         `(#t                  ,(↦ ['x 1]))))
  (check-equal? (car (-->>₁b `((∨ (≤ x 2) (≤ x 3)) ,(↦ ['x 1]))))
                (set         `(#t                  ,(↦ ['x 1])))))


(define-reduction (-->₁c -->₁a -->₁b)
  #:do [(define σ? map?)
        (define ((σ=? σ) σ′) (equal? σ σ′))]

  [`(skip ,σ)
   σ]

  [`((≔ ,x ,a) ,σ)
   `(,a′ ,(? σ=? σ)) ← (-->₁a `(,a ,σ))
   `((≔ ,x ,a′) ,σ)]

  [`((≔ ,x ,(? number? m)) ,σ)
   (σ x m)]

  [`((seq ,c₀ ,c₁) ,σ)
   `(,c₀′ ,σ′) ← (-->₁c `(,c₀ ,σ))
   `((seq ,c₀′ ,c₁) ,σ′)]

  [`((seq ,c₀ ,c₁) ,σ)
   (? σ? σ′) ← (-->₁c `(,c₀ ,σ))
   `(,c₁ ,σ′)]

  [`((if ,b ,c₀ ,c₁) ,σ)
   `(,b′ ,(? σ=? σ)) ← (-->₁b `(,b ,σ))
   `((if ,b′ ,c₀ ,c₁) ,σ)]

  [`((if #t ,c₀ ,c₁) ,σ)
   `(,c₀ ,σ)]

  [`((if #f ,c₀ ,c₁) ,σ)
   `(,c₁ ,σ)]

  [`((while ,b ,c) ,σ)
   `((if ,b
       (seq ,c (while ,b ,c))
       skip) ,σ)])

(define step₁-c (let ([reducer₁-a (reducer-of (-->₁a))])
                  (call-with-values
                   (λ () (-->₁c reducer₁-a (reducer-of (-->₁b reducer₁-a))))
                   compose1)))
(define -->>₁c (repeated step₁-c))

(define ((~₁c c₀ c₁) σ)
  (equal? (step₁-c `(,c₀ ,σ)) (step₁-c `(,c₁ ,σ))))

(module+ test
  (check-equal? (step₁-c `(skip ,(↦ ['x 1])))
                (set             (↦ ['x 1])))
  (check-equal? (step₁-c `((≔ x (+ x 1)) ,(↦ ['x 1])))
                (set     `((≔ x (+ 1 1)) ,(↦ ['x 1]))))
  (check-equal? (step₁-c `((seq (≔ x (+ x 1)) (≔ y (+ y x)))
                           ,(↦ ['x 1] ['y 1])))
                (set     `((seq (≔ x (+ 1 1)) (≔ y (+ y x)))
                           ,(↦ ['x 1] ['y 1]))))
  (check-equal? (step₁-c `((if (≤ x 1)
                             (≔ x (+ x 1))
                             skip) ,(↦ ['x 1])))
                (set     `((if (≤ 1 1)
                             (≔ x (+ x 1))
                             skip) ,(↦ ['x 1]))))
  (check-equal? (step₁-c `((if (≤ x 1)
                             (≔ x (+ x 1))
                             skip) ,(↦ ['x 2])))
                (set     `((if (≤ 2 1)
                             (≔ x (+ x 1))
                             skip) ,(↦ ['x 2]))))
  (check-equal? (step₁-c `((while (¬ (= x 0))
                             (seq (≔ sum (+ sum x))
                                  (≔ x (- x 1))))
                           ,(↦ ['x 10] ['sum 0])))
                (set     `((if (¬ (= x 0))
                             (seq
                              (seq (≔ sum (+ sum x))
                                   (≔ x (- x 1)))
                              (while (¬ (= x 0))
                                (seq (≔ sum (+ sum x))
                                     (≔ x (- x 1)))))
                             skip)
                           ,(↦ ['x 10] ['sum 0]))))

  (check-equal? (car (-->>₁c `(skip ,(↦ ['x 1]))))
                (set                 (↦ ['x 1])))
  (check-equal? (car (-->>₁c `((≔ x (+ x 1)) ,(↦ ['x 1]))))
                (set                          (↦ ['x 2])))
  (check-equal? (car (-->>₁c `((seq (≔ x (+ x 1))
                                    (≔ y (+ y x))) ,(↦ ['x 1] ['y 1]))))
                (set                                (↦ ['x 2] ['y 3])))
  (check-equal? (car (-->>₁c `((if (≤ x 1)
                                 (≔ x (+ x 1))
                                 skip) ,(↦ ['x 1]))))
                (set                    (↦ ['x 2])))
  (check-equal? (car (-->>₁c `((if (≤ x 1)
                                 (≔ x (+ x 1))
                                 skip) ,(↦ ['x 2]))))
                (set                    (↦ ['x 2])))
  (check-equal? (car (-->>₁c `((while (¬ (= x 0))
                                 (seq (≔ sum (+ sum x))
                                      (≔ x (- x 1))))
                               ,(↦ ['x 10] ['sum  0]))))
                (set            (↦ ['x  0] ['sum 55]))))

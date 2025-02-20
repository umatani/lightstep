#lang racket
(require lightstep/base)

(module+ test (require rackunit))

;;=============================================================================
;; 2.2 The evaluation of arithmetic expressions

(define-reduction (-->a-rules -->a)
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

(define-values (mrun-a reducer-a) (invoke-unit (-->a-rules reducer-a)))
(define -->a (compose1 mrun-a reducer-a))

(define ((~a a₀ a₁) σ)
  (equal? (-->a `(,a₀ ,σ)) (-->a `(,a₁ ,σ))))

(module+ test
  (check-equal? (-->a `(3 ,(↦))) (set 3))
  (check-equal? (-->a `(y ,(↦ ['x 3] ['y 2]))) (set 2))
  (check-equal? (-->a `((+ x 1) ,(↦ ['x 3] ['y 2]))) (set 4))
  (check-equal? (-->a `((+ x y) ,(↦ ['x 3] ['y 2]))) (set 5))
  (check-equal? (-->a `((- x y) ,(↦ ['x 3] ['y 2]))) (set 1))
  (check-equal? (-->a `((× x y) ,(↦ ['x 3] ['y 2]))) (set 6))

  (check-equal? (-->a `((+ (+ Init 5) (+ 7 9)) ,(↦ ['Init 0]))) (set 21)))

;;=============================================================================
;; 2.3 The evaluation of boolean expressions

(define-reduction (-->b-rules -->a -->b)
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

(define-values (mrun-b reducer-b)
  (invoke-unit (-->b-rules reducer-a reducer-b)))
(define -->b (compose1 mrun-b reducer-b))

(define ((~b b₀ b₁) σ)
  (equal? (-->b `(,b₀ ,σ)) (-->b `(,b₁ ,σ))))

(module+ test
  (check-equal? (-->b `(#t ,(↦))) (set #t))
  (check-equal? (-->b `(#f ,(↦))) (set #f))
  (check-equal? (-->b `((= x 1) ,(↦ ['x 1]))) (set #t))
  (check-equal? (-->b `((= x 1) ,(↦ ['x 2]))) (set #f))
  (check-equal? (-->b `((≤ x 0) ,(↦ ['x 1]))) (set #f))
  (check-equal? (-->b `((≤ x 3) ,(↦ ['x 2]))) (set #t))
  (check-equal? (-->b `((¬ (≤ x 0)) ,(↦ ['x 1]))) (set #t))
  (check-equal? (-->b `((¬ (≤ x 3)) ,(↦ ['x 2]))) (set #f))
  (check-equal? (-->b `((∧ (≤ x 0) (≤ x 3)) ,(↦ ['x 1]))) (set #f))
  (check-equal? (-->b `((∧ (≤ x 2) (≤ x 3)) ,(↦ ['x 1]))) (set #t))
  (check-equal? (-->b `((∨ (≤ x -1) (≤ x 0)) ,(↦ ['x 1]))) (set #f))
  (check-equal? (-->b `((∨ (≤ x 0) (≤ x 3)) ,(↦ ['x 1]))) (set #t))
  (check-equal? (-->b `((∨ (≤ x 2) (≤ x 3)) ,(↦ ['x 1]))) (set #t)))

(module+ left-first-sequential
  (require rackunit)

  (define-reduction (-->b′-rules -->a -->b′) #:super (-->b-rules -->a -->b′)
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

  (define-values (mrun-b′ reducer-b′)
    (invoke-unit (-->b′-rules reducer-a reducer-b′)))
  (define -->b′ (compose1 mrun-b′ reducer-b′))

  (check-equal? (-->b′ `(#t ,(↦))) (set #t))
  (check-equal? (-->b′ `(#f ,(↦))) (set #f))
  (check-equal? (-->b′ `((= x 1) ,(↦ ['x 1]))) (set #t))
  (check-equal? (-->b′ `((= x 1) ,(↦ ['x 2]))) (set #f))
  (check-equal? (-->b′ `((≤ x 0) ,(↦ ['x 1]))) (set #f))
  (check-equal? (-->b′ `((≤ x 3) ,(↦ ['x 2]))) (set #t))
  (check-equal? (-->b′ `((¬ (≤ x 0)) ,(↦ ['x 1]))) (set #t))
  (check-equal? (-->b′ `((¬ (≤ x 3)) ,(↦ ['x 2]))) (set #f))
  (check-equal? (-->b′ `((∧ (≤ x 0) (≤ x 3)) ,(↦ ['x 1]))) (set #f))
  (check-equal? (-->b′ `((∧ (≤ x 2) (≤ x 3)) ,(↦ ['x 1]))) (set #t))
  (check-equal? (-->b′ `((∨ (≤ x -1) (≤ x 0)) ,(↦ ['x 1]))) (set #f))
  (check-equal? (-->b′ `((∨ (≤ x 0) (≤ x 3)) ,(↦ ['x 1]))) (set #t))
  (check-equal? (-->b′ `((∨ (≤ x 2) (≤ x 3)) ,(↦ ['x 1]))) (set #t)))

(module+ parallel-or
  (require rackunit)

  (define-reduction (-->b′-rules -->a -->b′) #:super (-->b-rules -->a -->b′)
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

  (define-values (mrun-b′ reducer-b′)
    (invoke-unit (-->b′-rules reducer-a reducer-b′)))
  (define -->b′ (compose1 mrun-b′ reducer-b′))

  (check-equal? (-->b′ `(#t ,(↦))) (set #t))
  (check-equal? (-->b′ `(#f ,(↦))) (set #f))
  (check-equal? (-->b′ `((= x 1) ,(↦ ['x 1]))) (set #t))
  (check-equal? (-->b′ `((= x 1) ,(↦ ['x 2]))) (set #f))
  (check-equal? (-->b′ `((≤ x 0) ,(↦ ['x 1]))) (set #f))
  (check-equal? (-->b′ `((≤ x 3) ,(↦ ['x 2]))) (set #t))
  (check-equal? (-->b′ `((¬ (≤ x 0)) ,(↦ ['x 1]))) (set #t))
  (check-equal? (-->b′ `((¬ (≤ x 3)) ,(↦ ['x 2]))) (set #f))
  (check-equal? (-->b′ `((∧ (≤ x 0) (≤ x 3)) ,(↦ ['x 1]))) (set #f))
  (check-equal? (-->b′ `((∧ (≤ x 2) (≤ x 3)) ,(↦ ['x 1]))) (set #t))
  (check-equal? (-->b′ `((∨ (≤ x -1) (≤ x 0)) ,(↦ ['x 1]))) (set #f))
  (check-equal? (-->b′ `((∨ (≤ x 0) (≤ x 3)) ,(↦ ['x 1]))) (set #t))
  (check-equal? (-->b′ `((∨ (≤ x 2) (≤ x 3)) ,(↦ ['x 1]))) (set #t)))


;;=============================================================================
;; 2.4 The execution of commands

(define-reduction (-->c-rules -->a -->b -->c)
  [`(skip ,σ)
   σ
   "skip"]

  [`((≔ ,X ,a) ,σ)
   m ← (-->a `(,a ,σ))
   (σ X m)
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

(define-values (mrun-c reducer-c)
  (invoke-unit (-->c-rules reducer-a reducer-b reducer-c)))
(define -->c (compose1 mrun-c reducer-c))

(define ((~c c₀ c₁) σ)
  (equal? (-->c `(,c₀ ,σ)) (-->c `(,c₁ ,σ))))

(module+ test
  (check-equal? (-->c `(skip ,(↦ ['x 1]))) (set (↦ ['x 1])))
  (check-equal? (-->c `((≔ x (+ x 1)) ,(↦ ['x 1]))) (set (↦ ['x 2])))
  (check-equal? (-->c `((seq (≔ x (+ x 1)) (≔ y (+ y x))) ,(↦ ['x 1] ['y 1])))
                (set (↦ ['x 2] ['y 3])))
  (check-equal? (-->c `((if (≤ x 1)
                          (≔ x (+ x 1))
                          skip) ,(↦ ['x 1])))
                (set (↦ ['x 2])))
  (check-equal? (-->c `((if (≤ x 1)
                          (≔ x (+ x 1))
                          skip) ,(↦ ['x 2])))
                (set (↦ ['x 2])))
  (check-equal? (-->c `((while (¬ (= x 0))
                          (seq (≔ sum (+ sum x))
                               (≔ x (- x 1))))
                        ,(↦ ['x 10] ['sum 0])))
                (set (↦ ['x 0] ['sum 55]))))


;;=============================================================================
;; 2.6 Alternative semantics

(define-reduction (-->₁a-rules -->₁a)
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

(define-values (mrun₁-a reducer₁-a) (invoke-unit (-->₁a-rules reducer₁-a)))
(define -->₁a (compose1 mrun₁-a reducer₁-a))
(define -->>₁a (repeated -->₁a))

(define ((~₁a a₀ a₁) σ)
  (equal? (-->₁a `(,a₀ ,σ)) (-->₁a `(,a₁ ,σ))))

(module+ test
  (check-equal? (-->₁a `(3 ,(↦))) ∅)
  (check-equal? (-->₁a `(y ,(↦ ['x 3] ['y 2])))
                (set   `(2 ,(↦ ['x 3] ['y 2]))))
  (check-equal? (-->₁a `((+ x 1) ,(↦ ['x 3] ['y 2])))
                (set   `((+ 3 1) ,(↦ ['x 3] ['y 2]))))
  (check-equal? (-->₁a `((+ x y) ,(↦ ['x 3] ['y 2])))
                (set   `((+ 3 y) ,(↦ ['x 3] ['y 2]))))
  (check-equal? (-->₁a `((- x y) ,(↦ ['x 3] ['y 2])))
                (set   `((- 3 y) ,(↦ ['x 3] ['y 2]))))
  (check-equal? (-->₁a `((× x y) ,(↦ ['x 3] ['y 2])))
                (set   `((× 3 y) ,(↦ ['x 3] ['y 2]))))
  (check-equal? (-->₁a `((+ (+ Init 5) (+ 7 9)) ,(↦ ['Init 0])))
                (set   `((+ (+ 0 5) (+ 7 9))    ,(↦ ['Init 0]))))

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


(define-reduction (-->₁b-rules -->₁a -->₁b)
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

(define-values (mrun₁-b reducer₁-b)
  (invoke-unit (-->₁b-rules reducer₁-a reducer₁-b)))
(define -->₁b (compose1 mrun₁-b reducer₁-b))
(define -->>₁b (repeated -->₁b))

(define ((~b₁ b₀ b₁) σ)
  (equal? (-->₁b `(,b₀ ,σ)) (-->₁b `(,b₁ ,σ))))

(module+ test
  (check-equal? (-->₁b `(#t ,(↦))) ∅)
  (check-equal? (-->₁b `(#f ,(↦))) ∅)
  (check-equal? (-->₁b `((= x 1) ,(↦ ['x 1])))
                (set   `((= 1 1) ,(↦ ['x 1]))))
  (check-equal? (-->₁b `((= x 1) ,(↦ ['x 2])))
                (set   `((= 2 1) ,(↦ ['x 2]))))
  (check-equal? (-->₁b `((≤ x 0) ,(↦ ['x 1])))
                (set   `((≤ 1 0) ,(↦ ['x 1]))))
  (check-equal? (-->₁b `((≤ x 3) ,(↦ ['x 2])))
                (set   `((≤ 2 3) ,(↦ ['x 2]))))
  (check-equal? (-->₁b `((¬ (≤ x 0)) ,(↦ ['x 1])))
                (set   `((¬ (≤ 1 0)) ,(↦ ['x 1]))))
  (check-equal? (-->₁b `((¬ (≤ x 3)) ,(↦ ['x 2])))
                (set   `((¬ (≤ 2 3)) ,(↦ ['x 2]))))
  (check-equal? (-->₁b `((∧ (≤ x 0) (≤ x 3)) ,(↦ ['x 1])))
                (set   `((∧ (≤ 1 0) (≤ x 3)) ,(↦ ['x 1]))))
  (check-equal? (-->₁b `((∧ (≤ x 2) (≤ x 3)) ,(↦ ['x 1])))
                (set   `((∧ (≤ 1 2) (≤ x 3)) ,(↦ ['x 1]))))
  (check-equal? (-->₁b `((∨ (≤ x -1) (≤ x 0)) ,(↦ ['x 1])))
                (set   `((∨ (≤ 1 -1) (≤ x 0)) ,(↦ ['x 1]))))
  (check-equal? (-->₁b `((∨ (≤ x 0) (≤ x 3)) ,(↦ ['x 1])))
                (set   `((∨ (≤ 1 0) (≤ x 3)) ,(↦ ['x 1]))))
  (check-equal? (-->₁b `((∨ (≤ x 2) (≤ x 3)) ,(↦ ['x 1])))
                (set   `((∨ (≤ 1 2) (≤ x 3)) ,(↦ ['x 1]))))

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


(define-reduction (-->₁c-rules -->₁a -->₁b -->₁c)
  #:do [(define σ? map?)
        (define ((σ=? σ) σ′) (equal? σ σ′))]

  [`(skip ,σ)
   σ]

  [`((≔ ,X ,a) ,σ)
   `(,a′ ,(? σ=? σ)) ← (-->₁a `(,a ,σ))
   `((≔ ,X ,a′) ,σ)]

  [`((≔ ,X ,(? number? m)) ,σ)
   (σ X m)]

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

(define-values (mrun₁-c reducer₁-c)
  (invoke-unit (-->₁c-rules reducer₁-a reducer₁-b reducer₁-c)))
(define -->₁c (compose1 mrun₁-c reducer₁-c))
(define -->>₁c (repeated -->₁c))

(define ((~₁c c₀ c₁) σ)
  (equal? (-->₁c `(,c₀ ,σ)) (-->₁c `(,c₁ ,σ))))

(module+ test
  (check-equal? (-->₁c `(skip ,(↦ ['x 1])))
                (set           (↦ ['x 1])))
  (check-equal? (-->₁c `((≔ x (+ x 1)) ,(↦ ['x 1])))
                (set   `((≔ x (+ 1 1)) ,(↦ ['x 1]))))
  (check-equal? (-->₁c `((seq (≔ x (+ x 1)) (≔ y (+ y x))) ,(↦ ['x 1] ['y 1])))
                (set   `((seq (≔ x (+ 1 1)) (≔ y (+ y x))) ,(↦ ['x 1] ['y 1]))))
  (check-equal? (-->₁c `((if (≤ x 1)
                           (≔ x (+ x 1))
                           skip) ,(↦ ['x 1])))
                (set   `((if (≤ 1 1)
                           (≔ x (+ x 1))
                           skip) ,(↦ ['x 1]))))
  (check-equal? (-->₁c `((if (≤ x 1)
                           (≔ x (+ x 1))
                           skip) ,(↦ ['x 2])))
                (set   `((if (≤ 2 1)
                           (≔ x (+ x 1))
                           skip) ,(↦ ['x 2]))))
  (check-equal? (-->₁c `((while (¬ (= x 0))
                           (seq (≔ sum (+ sum x))
                                (≔ x (- x 1))))
                         ,(↦ ['x 10] ['sum 0])))
                (set   `((if (¬ (= x 0))
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

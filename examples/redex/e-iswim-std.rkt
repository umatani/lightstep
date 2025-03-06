#lang racket/base
(require lightstep/base lightstep/syntax
         (only-in "iswim.rkt" βv-rule)
         (only-in "iswim-std.rkt" ECxt)
         (only-in "e-iswim.rkt" [E-ISWIM orig-E-ISWIM] δ-rule δerr-rule))

;;=============================================================================
;; 8.1 Standard Reduction for Error ISWIM 

(define-language E-ISWIM #:super orig-E-ISWIM)

(define-reduction (ẽ) #:super [(βv-rule) (δ-rule) (δerr-rule)])

(define-reduction (⊢->ẽ)
  #:do [(define →ẽ (reducer-of (ẽ)))]
  [(ECxt m)
   #:when (M? m)
   M′ ← (→ẽ m)
   (ECxt M′)]
  [(ECxt e)
   `(err ,L) ← e
   `(err ,L)])

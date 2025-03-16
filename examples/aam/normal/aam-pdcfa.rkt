#lang racket
(require lightstep/base lightstep/transformers)

(module+ test (require rackunit))

;; Abstracting Abstract Machines from:
;;   https://dvanhorn.github.io/redex-aam-tutorial/

;; Continuation を Abstracting Abstract Control 版に．
;; PCFσ*ではなく，KがメタスタックのままのPCFσベースの方が適切(？)

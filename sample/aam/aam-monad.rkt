#lang racket
(require lightstep/base)

;; Abstracting Abstract Machines from:
;;   https://dvanhorn.github.io/redex-aam-tutorial/

;; reduction body にカスタム monad を利用

#lang racket
(require lightstep/base)

(define i 0)
(match '(1 2 3 4 5)
  [`(,x ... ,y ,z ..,i)
   (list x y z)])

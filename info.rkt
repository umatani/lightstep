#lang info
(define collection "lightstep")
(define deps '("base" "rackunit-lib"))
(define build-deps '("scribble-lib" "racket-doc" "rackunit-lib"))
(define scribblings '(("scribblings/lightstep.scrbl" ())))
(define pkg-desc "Lightweight Reduction Engine")
(define version "0.1")
(define pkg-authors '("Seiji Umatani"))
(define license '(Apache-2.0 OR MIT))

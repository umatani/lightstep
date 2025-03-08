#lang racket/base

(require "base.rkt"
         "syntax.rkt"
         "transformers.rkt")
(provide (all-from-out "base.rkt")
         (all-from-out "syntax.rkt")
         (all-from-out "transformers.rkt"))

(module+ test
  (require (submod lightstep/nondet test))
  (require (submod lightstep/transformers test))
  (require (submod lightstep/syntax test))

  (require (submod lightstep/examples/unit-tests scope2))

  ;; SAC'24
  (require (submod lightstep/examples/design1 test))
  (require (submod lightstep/examples/design2 test))
  (require (submod lightstep/examples/design3 test))
  (require (submod lightstep/examples/design4 test))
  (require (submod lightstep/examples/design5 test))

  ;; winskel
  (require (submod lightstep/examples/winskel/imp test))
  (require (submod lightstep/examples/winskel/imp left-first-sequential))
  (require (submod lightstep/examples/winskel/imp parallel-or))
  (require (submod lightstep/examples/winskel/imp-state test))
  (require (submod lightstep/examples/winskel/imp-state left-first-sequential))
  (require (submod lightstep/examples/winskel/imp-state parallel-or))

  ;; redex
  (require (submod lightstep/examples/redex/b test))
  (require (submod lightstep/examples/redex/lam test))
  (require (submod lightstep/examples/redex/iswim test))
  (require (submod lightstep/examples/redex/iswim-std test))
  (require (submod lightstep/examples/redex/cc test))
  (require (submod lightstep/examples/redex/scc test))
  (require (submod lightstep/examples/redex/ck test))
  (require (submod lightstep/examples/redex/cek test))
  (require (submod lightstep/examples/redex/secd test))
  (require (submod lightstep/examples/redex/secd2 test))
  (require (submod lightstep/examples/redex/secd-tco test))
  (require (submod lightstep/examples/redex/cek-ss test))
  (require (submod lightstep/examples/redex/secd-tco-ss test))
  (require (submod lightstep/examples/redex/e-iswim test))
  (require (submod lightstep/examples/redex/e-iswim-std test))
  (require (submod lightstep/examples/redex/h-iswim test))
  (require (submod lightstep/examples/redex/h-iswim-std test))
  (require (submod lightstep/examples/redex/cc+h test))
  (require (submod lightstep/examples/redex/chc test))
  (require (submod lightstep/examples/redex/c-iswim test))
  (require (submod lightstep/examples/redex/c-iswim-std test))

  ;; aam
  (require (submod lightstep/examples/aam/common test))
  (require (submod lightstep/examples/aam/l test))
  (require (submod lightstep/examples/aam/pcf test))
  (require (submod lightstep/examples/aam/pcf-bigstep test))
  (require (submod lightstep/examples/aam/l0 test))
  (require (submod lightstep/examples/aam/l1 test))
  (require (submod lightstep/examples/aam/pcf-rho test))
  (require (submod lightstep/examples/aam/pcf-varsigma test))
  (require (submod lightstep/examples/aam/pcf-sigma test))
  (require (submod lightstep/examples/aam/pcf-sigma-alloc test))
  (require (submod lightstep/examples/aam/pcf-sigma-star test))
  )

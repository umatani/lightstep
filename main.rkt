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
  (require (submod lightstep/examples/winskel/imp-state test))
  (require (submod lightstep/examples/winskel/imp-state left-first-sequential))
  (require (submod lightstep/examples/winskel/imp-state parallel-or))

  ;; redex
  (require (submod lightstep/examples/redex/b test))
  (require (submod lightstep/examples/redex/lam test))
  (require (submod lightstep/examples/redex/iswim test))
  (require (submod lightstep/examples/redex/iswim2 test))
  (require (submod lightstep/examples/redex/cc test))
  (require (submod lightstep/examples/redex/scc test))
  (require (submod lightstep/examples/redex/ck test))
  (require (submod lightstep/examples/redex/cek test))
  (require (submod lightstep/examples/redex/secd test))

  ;; aam
  (require (submod lightstep/examples/aam/common test))
  (require (submod lightstep/examples/aam/aam1-3_3 L test))
  (require (submod lightstep/examples/aam/aam1-3_3 test))
  (require (submod lightstep/examples/aam/aam3_4 PCF⇓))
  (require (submod lightstep/examples/aam/aam3_4 PCF⇓))
  (require (submod lightstep/examples/aam/aam3_4 §3.5 L₀))
  (require (submod lightstep/examples/aam/aam3_4 §3.5 L₁))
  (require (submod lightstep/examples/aam/aam3_4 PCFρ))
  (require (submod lightstep/examples/aam/aam3_4 PCFς))
  (require (submod lightstep/examples/aam/aam3_4 PCFσ))
  (require (submod lightstep/examples/aam/aam3_4 PCFσ/alloc))
  (require (submod lightstep/examples/aam/aam3_4 PCFσ*)))

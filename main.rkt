#lang racket/base

(require "base.rkt")
(provide (all-from-out "base.rkt"))

(module+ test
  (require (submod lightstep/nondet test))
  (require (submod lightstep/syntax test))

  (require (submod lightstep/sample/unit-tests scope2))

  ;; SAC'24
  (require (submod lightstep/sample/design1 test))
  (require (submod lightstep/sample/design2 test))
  (require (submod lightstep/sample/design3 test))
  (require (submod lightstep/sample/design4 test))
  (require (submod lightstep/sample/design5 test))

  ;; winskel
  (require (submod lightstep/sample/winskel/imp test))
  (require (submod lightstep/sample/winskel/imp-state test))
  (require (submod lightstep/sample/winskel/imp-state left-first-sequential))
  (require (submod lightstep/sample/winskel/imp-state parallel-or))

  ;; redex
  (require (submod lightstep/sample/redex/b test))
  (require (submod lightstep/sample/redex/lam test))

  ;; aam
  (require (submod lightstep/sample/aam/common test))
  (require (submod lightstep/sample/aam/aam1-3_3 L test))
  (require (submod lightstep/sample/aam/aam1-3_3 test))
  (require (submod lightstep/sample/aam/aam3_4 PCF⇓))
  (require (submod lightstep/sample/aam/aam3_4 PCF⇓))
  (require (submod lightstep/sample/aam/aam3_4 §3.5 L₀))
  (require (submod lightstep/sample/aam/aam3_4 §3.5 L₁))
  (require (submod lightstep/sample/aam/aam3_4 PCFρ))
  (require (submod lightstep/sample/aam/aam3_4 PCFς))
  (require (submod lightstep/sample/aam/aam3_4 PCFσ))

  )
